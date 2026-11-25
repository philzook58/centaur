import Mathlib
import ai_stewart
open Real

#check (proof1 : deriv (fun x => sin x) = cos)

noncomputable section Chap1

variable (h : Real)
variable (hh : h ≠ 0)
def f (x : Real) : Real := 2 * x^2 - 5 * x + 1

example (x : Real) : (f (x + h) - f x) / h = 4 * x + 2 * h - 5 := by
  calc
    _ = (2 * (x + h)^2 - 5 * (x + h) + 1 - (2 * x^2 - 5 * x + 1)) / h := proof3
    _ = (2 * (x ^ 2 + 2 * x * h + h ^ 2 ) - 5* (x + h) + 1 - (2 * x^2 - 5 * x + 1)) / h := proof4
    _ = (4 * x * h + 2 * h^2 - 5 * h) / h := proof5
    _ = 4 * x + 2 * h - 5 := proof6


-- find the domain of sqrt (x + 2)
-- How would i even fomrulate that?

example (x : Real) : 0 <= x + 2 <-> -2 <= x := by constructor <;> intro <;> linarith


def f1 (x : Real) := if x <= 1 then 1-x else x^2

-- what tactics to use to derive the value automaticall?
-- Is this the best way to do this?
def f10 : {z // f1 0 = z} := by
  exact ⟨_, by norm_num [f1]; rfl⟩

#print f10
-- how can I just simply request an answer? Run a tactic simply?
#norm_num [f1] : f1 0


example (x : Real) (h : x >= 0) : |x| = x := by exact abs_of_nonneg h


-- Hmm. the other direction might be better because a simplifiecation direction?
def even (f : Real -> Real) := forall x : Real, f x = f (-x)
def odd (f : Real -> Real) := forall x : Real, f x = - (f (-x))

#check Function.Even
#print Function.Even
#check Function.Odd

example : Function.Even (fun x : Real => x^2) := by simp [Function.Even]
example : Function.Odd (fun x : Real => x^3) := by
  intro
  ring


def increasing (f : Real -> Real) := forall x y, x < y -> (f x) < (f y)
def decreasing (f : Real -> Real) := forall x y, x < y -> f x > f y

#print StrictMono
#print Monotone
#print Antitone
#print StrictAnti

-- affine. But stewart says linear, so suck it.
def linear (f : Real -> Real) := exists m b, forall x, f x = m * x + b

def polynomial (f : Real -> Real) := exists p : Polynomial Real, forall x, f x = p.eval x
def quadratic (f : Real -> Real) := exists a b c, forall x, f x = a * x^2 + b * x + c


-- plot? Do it in floats? Send it into the infoview as a base64 image
-- I don't see anything in the infoview
#plot (fun t : Float => 0 + 4*t - 2 * t^2)

-- #plot (fun t : Real => 0 + 4*t - 2 * t^2)

#norm_num (2 : Real) ^ (1 / 3 : Real)  -- returns 1???
#eval Float.pow 2 (1/3)


-- is simp here bad form? exact? grind? What should be my default?
example : forall x, -1 <= sin x /\ sin x <= 1 := by simp [neg_one_le_sin, sin_le_one]
example : forall x, sin (x + π) = - (sin x) := by simp


def comp (f g : Real -> Real) := fun x => f (g x)
#check _ ∘ _
#print Function.comp


#plot fun x => Float.sqrt (8 - 2 * x^2)

example : forall (x a b : Real) (h : x > 0), x ^(a + b) = x^a * x ^ b := fun _ a b h => Real.rpow_add h a b

#check Function.invFun

example (f : Real -> Real) (h : Function.Injective f) :
  (Function.invFun f) ∘ f = id := Function.invFun_comp h


-- exponentiating negatives is goofy
--example : Function.invFun (fun x : Real => x ^ 3 + 2) =
--   (fun y : Real => (y - 2) ^ (1/3 : Real)) := by




end Chap1


open Function

noncomputable section Chap2

open Filter
open scoped Topology

--example : lim (x -> 2) (fun x => x^2 - x + 2) = 4 := by
--  norm_num

-- \nhds to type 𝓝
#check 𝓝
--#check 𝓝[≠]
#check nhds
#check nhdd_ne
-- Is this the friendliest notation we have?

-- This is super non intuitive. What is all this jun. How would I have known to do it?
-- when should I use fun_prop? is that a mathlib thing?
-- What is in the fun_prop database?
example : Tendsto (fun x : Real => x^2 - x + 2) (nhds 2) (nhds 4) := by
  have hc : Continuous (fun x : Real => x^2 - x + 2) := by fun_prop
  convert (hc.continuousAt (x := (2 : Real))).tendsto using 1
  norm_num

#check Continuous.tendsto
#print Continuous

#print_fun_prop_theorems Real.sin

def lim (x : Real) f (v : Real) := Tendsto f (nhds x) (nhds v)

-- is there a nicer way to write positive  del and eps?
-- hmm so using the symbols gets me more syntax? Any other cute tricks ?
-- ∃!   (· ^ 2)
-- ∀ᶠ y in 𝓝 x   -- filter quantifier?
def naivelim (x : Real) (f : Real -> Real) (v : Real) :=
  ∀ eps > 0,
  ∃ del > 0,
  forall y, |x - y| < del ->
  |f y - v| < eps

example : lim = naivelim := proof8
-- That's pretty cool.




end Chap2
