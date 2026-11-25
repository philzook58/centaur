#!/usr/bin/env python3
"""Wait for project changes, print JSON, and exit immediately by default.

Linux, Python standard library only. Watches the entire tree, including hidden
directories. Keeps a source baseline outside the project and emits bounded diffs.
Run again after handling a batch; re-read current files before edits.

--compact prints one short line per event (changed lines only, with line numbers, no JSON or
context) and nothing when idle; --loop keeps watching and prints one line per event. Together
they suit streaming monitors whose notifications truncate long events.
"""

import argparse
import ctypes
import errno
import difflib
import hashlib
import tempfile
import json
import os
from pathlib import Path
import select
import struct
import sys
import time


def compact(event):
    """One line per event: changed lines with new-file line numbers; None when nothing to say."""
    if event.get("status") != "changed":
        return None
    parts = []
    for path in event.get("paths", []):
        if ".tmp." in path or path.split(os.sep, 1)[0] in {".git", ".lake"}:
            continue  # Atomic-save temporaries and generated trees.
        diff = event.get("diffs", {}).get(path)
        if diff is None:
            if path in event.get("read_required", []):
                parts.append(f"[{path}] diff too large: read it")
            else:
                parts.append(f"[{path}] no content change")
            continue
        out, line = [], 0
        for d in diff.splitlines():
            if d.startswith(("---", "+++")):
                continue
            if d.startswith("@@"):
                line = int(d.split("+", 1)[1].split(",", 1)[0].split(" ", 1)[0])
            elif d.startswith("+"):
                out.append(f"L{line}+ {d[1:].strip()}")
                line += 1
            elif d.startswith("-"):
                out.append(f"L{line}- {d[1:].strip()}")
            else:
                line += 1
        parts.append(f"[{path}] " + (" ⏎ ".join(out) or "whitespace only"))
    if event.get("rescan_required"):
        parts.append("rescan required (inotify overflow)")
    return " || ".join(parts) or None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", nargs="?", default=".")
    parser.add_argument("--debounce", type=float, default=0)
    parser.add_argument("--timeout", type=float, default=55)
    parser.add_argument("--state", type=Path, help="Baseline file; defaults to /tmp per project")
    parser.add_argument("--baseline", action="store_true", help="Record current state and exit")
    parser.add_argument("--compact", action="store_true", help="One short line per event")
    parser.add_argument("--loop", action="store_true", help="Keep watching; one line per event")
    args = parser.parse_args()
    if args.debounce < 0 or args.timeout <= 0:
        parser.error("debounce must be nonnegative and timeout must be positive")
    if args.loop and args.baseline:
        parser.error("--loop and --baseline are exclusive")
    while True:
        result = watch_once(args, parser)
        if args.compact:
            line = compact(result)
            if line:
                print(line, flush=True)
        elif not (args.loop and result.get("status") == "idle"):
            print(json.dumps(result), flush=True)
        if not args.loop:
            return


def watch_once(args, parser):
    """Wait for one batch of changes (or the timeout) and return the event dict."""
    root = Path(args.root).resolve(strict=True)
    if not root.is_dir():
        parser.error("root must be a directory")
    key = hashlib.sha256(os.fsencode(root)).hexdigest()[:16]
    state_path = args.state or Path(tempfile.gettempdir()) / f"proof-watch-{os.getuid()}-{key}.json"
    text_suffixes = {".lean", ".md", ".toml", ".py", ".sh"}

    def snapshot():
        result = {}
        for base, directories, files in os.walk(root):
            # Generated trees are still watched live, but need no durable content baseline.
            directories[:] = [d for d in directories if d not in {".git", ".lake"}
                              and not os.path.islink(os.path.join(base, d))]
            for name in files:
                path = Path(base) / name
                if path.is_symlink() or path == state_path:
                    continue
                try:
                    stat = path.stat()
                    rel = str(path.relative_to(root))
                    item = {"stamp": [stat.st_mtime_ns, stat.st_size, stat.st_ino]}
                    if (path.suffix in text_suffixes and stat.st_size <= 512_000
                            and not any(part.startswith(".") and part != ".github"
                                        for part in Path(rel).parts)):
                        item["text"] = path.read_text(encoding="utf-8")
                    result[rel] = item
                except (FileNotFoundError, UnicodeError, PermissionError):
                    continue
        return result

    def save(current):
        state_path.parent.mkdir(parents=True, exist_ok=True)
        temporary = state_path.with_name(state_path.name + f".{os.getpid()}.tmp")
        with open(temporary, "w", encoding="utf-8", opener=lambda p, f: os.open(p, f, 0o600)) as out:
            json.dump(current, out)
        os.replace(temporary, state_path)

    def report(old, current, events=(), rescan=False):
        changed = []
        for name in sorted(old.keys() | current.keys()):
            before, after = old.get(name), current.get(name)
            if before is not None and after is not None:
                if "text" in before and "text" in after:
                    if before["text"] == after["text"]:
                        continue
                elif before["stamp"] == after["stamp"]:
                    continue
            changed.append(name)
        output = {"status": "changed", "paths": sorted(set(changed) | set(events)),
                  "rescan_required": rescan, "diffs": {}}
        budget = 16_000
        for name in changed:
            before, after = old.get(name, {}), current.get(name, {})
            if "text" not in before and "text" not in after:
                continue
            diff = "".join(difflib.unified_diff(
                before.get("text", "").splitlines(True), after.get("text", "").splitlines(True),
                fromfile=name, tofile=name, n=3))
            if len(diff) > budget:
                output.setdefault("read_required", []).append(name)
            else:
                output["diffs"][name] = diff
                budget -= len(diff)
        save(current)
        return output

    try:
        old = json.loads(state_path.read_text())
    except (FileNotFoundError, ValueError):
        old = None
    libc = ctypes.CDLL("libc.so.6", use_errno=True)
    fd = libc.inotify_init1(os.O_NONBLOCK | os.O_CLOEXEC)
    if fd < 0:
        raise OSError(ctypes.get_errno(), "inotify_init1 failed")
    paths = {}
    # Writes, attributes, moves, creation, deletion; never subscribe to reads.
    mask = 0x2 | 0x4 | 0x8 | 0x40 | 0x80 | 0x100 | 0x200 | 0x400 | 0x800

    def add_tree(path):
        for base, directories, _ in os.walk(path):
            directories[:] = [d for d in directories if not os.path.islink(os.path.join(base, d))]
            wd = libc.inotify_add_watch(fd, os.fsencode(base), mask)
            if wd < 0:
                error = ctypes.get_errno()
                if error == errno.ENOENT:
                    continue  # Directory disappeared during an atomic save/move.
                raise OSError(error, "Cannot watch " + base)
            paths[wd] = base

    try:
        add_tree(root)
        current = snapshot()
        if args.baseline or old is None:
            save(current)
            old = current
            if args.baseline:
                return {"status": "baseline"}
        elif current != old:
            result = report(old, current)
            old = current
            if result["paths"]:
                return result
        deadline = time.monotonic() + args.timeout
        first_event = None
        quiet_until = None
        changes = set()
        rescan = False
        while True:
            now = time.monotonic()
            # Return no later than 0.75s after the first event, even during a build.
            end = deadline if first_event is None else min(quiet_until, first_event + 0.75)
            if now >= end:
                break
            if not select.select([fd], [], [], end - now)[0]:
                continue
            while True:
                try:
                    data = os.read(fd, 1024 * 1024)
                except BlockingIOError:
                    break
                offset = 0
                while offset < len(data):
                    wd, event, _, length = struct.unpack_from("iIII", data, offset)
                    offset += 16
                    name = os.fsdecode(data[offset:offset + length].split(b"\0", 1)[0])
                    offset += length
                    if event & 0x4000:  # IN_Q_OVERFLOW: never silently lose changes.
                        rescan = True
                    elif event & 0x8000:  # IN_IGNORED
                        paths.pop(wd, None)
                        continue
                    elif wd in paths:
                        path = os.path.join(paths[wd], name)
                        changes.add(os.path.relpath(path, root))
                        if event & 0x40000000 and event & (0x100 | 0x80):
                            add_tree(path)
                    now = time.monotonic()
                    if first_event is None:
                        first_event = now
                    quiet_until = now + args.debounce
        if first_event is None:
            return {"status": "idle"}
        return report(old, snapshot(), changes, rescan)
    finally:
        os.close(fd)


if __name__ == "__main__":
    main()
