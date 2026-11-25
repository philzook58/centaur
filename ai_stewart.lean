import Mathlib
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts

open Real

theorem proof1 : deriv (fun x : ℝ ↦ sin x) = cos := Real.deriv_sin

theorem proof3 {a : ℝ} : a = a := rfl

theorem proof4 {x h : ℝ} :
    (2 * (x + h) ^ 2 - 5 * (x + h) + 1 - (2 * x ^ 2 - 5 * x + 1)) / h =
      (2 * (x ^ 2 + 2 * x * h + h ^ 2) - 5 * (x + h) + 1 -
        (2 * x ^ 2 - 5 * x + 1)) / h := by
  congr 1
  ring

-- Expand the numerator, then cancel the nonzero increment.
theorem proof5 {x h : ℝ} :
    (2 * (x ^ 2 + 2 * x * h + h ^ 2) - 5 * (x + h) + 1 -
      (2 * x ^ 2 - 5 * x + 1)) / h = (4 * x * h + 2 * h ^ 2 - 5 * h) / h := by
  congr 1
  ring

theorem proof6 {x h : ℝ} (hh : h ≠ 0 := by assumption) :
    (4 * x * h + 2 * h ^ 2 - 5 * h) / h = 4 * x + 2 * h - 5 := by
  apply (div_eq_iff hh).2
  ring

theorem proof2 {x h : ℝ} (hh : h ≠ 0 := by assumption) :
    ((2 * (x + h) ^ 2 - 5 * (x + h) + 1) - (2 * x ^ 2 - 5 * x + 1)) / h =
      4 * x + 2 * h - 5 := by
  apply (div_eq_iff hh).2
  ring

/-! ### Inverse of `x ↦ x ^ 3 + 2`

`Real.rpow` with a negative base is *not* the real cube root: for `x < 0`,
`x ^ y = exp (log x * y) * cos (y * π)`, so `(-1) ^ (1/3 : ℝ) = cos (π/3) = 1/2`.
Route for the counterexample: `invFun f 1 = -1` (since `f (-1) = 1` and `f` is injective),
but `(1 - 2) ^ (1/3) = 1/2`. -/

theorem cube_add_two_injective : Function.Injective (fun x : ℝ => x ^ 3 + 2) := by
  intro a b hab
  exact (Odd.strictMono_pow (by decide : Odd 3)).injective (by simpa using hab)

theorem cube_invFun_ne_rpow :
    Function.invFun (fun x : ℝ => x ^ 3 + 2) ≠ fun y => (y - 2) ^ (1 / 3 : ℝ) := by
  intro h
  have h1 := congrFun h 1
  have hl : Function.invFun (fun x : ℝ => x ^ 3 + 2) 1 = -1 := by
    have := Function.leftInverse_invFun cube_add_two_injective (-1 : ℝ)
    norm_num at this
    exact this
  rw [hl, show (1:ℝ) - 2 = -1 by norm_num, Real.rpow_def_of_neg (by norm_num)] at h1
  rw [show 1 / 3 * π = π / 3 by ring, Real.cos_pi_div_three] at h1
  norm_num at h1

/-- Corrected statement: real cube root via sign and absolute value.
Route: show `g` is a right inverse (`f (g y) = y`, split on the sign of `y - 2`),
then `invFun f (f (g y)) = g y` by injectivity. -/
theorem cube_invFun :
    Function.invFun (fun x : ℝ => x ^ 3 + 2) =
      fun y => Real.sign (y - 2) * |y - 2| ^ (1 / 3 : ℝ) := by
  funext y
  have key : (Real.sign (y - 2) * |y - 2| ^ (1 / 3 : ℝ)) ^ 3 + 2 = y := by
    have hc : (|y - 2| ^ (1 / 3 : ℝ)) ^ 3 = |y - 2| := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; norm_num
    rw [mul_pow, hc]
    rcases lt_trichotomy (y - 2) 0 with hy | hy | hy
    · rw [Real.sign_of_neg hy, abs_of_neg hy]; ring
    · rw [hy]; simp; linarith
    · rw [Real.sign_of_pos hy, abs_of_pos hy]; ring
  conv_lhs => rw [← key]
  exact Function.leftInverse_invFun cube_add_two_injective _

/-- ε–δ continuity-style limit ↔ `Tendsto`. Route: `Metric.tendsto_nhds_nhds` is exactly the
ε–δ statement with `dist`; on ℝ, `dist a b = |a - b|`, and `abs_sub_comm` flips `|x - y|`. -/
theorem epsdel_iff_tendsto {x v : ℝ} {f : ℝ → ℝ} :
    (∀ eps > 0, ∃ del > 0, ∀ y, |x - y| < del → |f y - v| < eps) ↔
      Filter.Tendsto f (nhds x) (nhds v) := by
  simp only [Metric.tendsto_nhds_nhds, Real.dist_eq, abs_sub_comm x]

/-- `lim = naivelim`, stated with both bodies unfolded (the AI file cannot import the human
definitions). Lean unfolds `lim`/`naivelim` when matching, so this fits the human statement.
Route: function extensionality three times, then `propext` of `epsdel_iff_tendsto`. -/
theorem proof8 :
    (fun (x : ℝ) (f : ℝ → ℝ) (v : ℝ) => Filter.Tendsto f (nhds x) (nhds v)) =
      fun x f v => ∀ eps > 0, ∃ del > 0, ∀ y, |x - y| < del → |f y - v| < eps := by
  funext x f v
  exact propext epsdel_iff_tendsto.symm

meta section

namespace AIPlot

open Lean ProofWidgets Recharts
open scoped ProofWidgets.Jsx

/-- Sample a floating-point function for an Infoview chart. This is a numerical visualization,
not a theorem about the corresponding real function. Nonfinite samples become gaps. -/
def plot (f : Float → Float) (lo : Float := -20) (hi : Float := 25) : Html := Id.run do
  let mut data : Array Json := #[]
  for i in [:401] do
    let x := lo + (hi - lo) * i.toFloat / 400
    let y := f x
    let value := if y.isFinite then toJson y else Json.null
    data := data.push (json% { x: $(toJson x), y: $value })
  return <LineChart width={600} height={360} data={data}>
    <XAxis domain?={#[toJson lo, toJson hi]} dataKey?="x" />
    <YAxis />
    <Line type={.linear} dataKey="y" stroke="#8884d8" dot?={Bool.false} />
  </LineChart>

end AIPlot

/-- Plot a `Float → Float` in Infoview. Defaults to [-20, 25]; use
`#plot (fun x : Float => x^2) from (-5) to 5` to choose the range. -/
macro "#plot " f:term " from " lo:term " to " hi:term : command =>
  `(run_cmd do
      Lean.logInfo (← Lean.Elab.Command.liftCoreM
        (Lean.MessageData.ofHtml (AIPlot.plot $f $lo $hi) "Function plot")))

/-- Plot a floating-point function on [-20, 25] in Infoview. -/
macro "#plot " f:term : command =>
  `(run_cmd do
      Lean.logInfo (← Lean.Elab.Command.liftCoreM
        (Lean.MessageData.ofHtml (AIPlot.plot $f) "Function plot")))

end
