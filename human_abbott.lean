import Mathlib
import ai_abbott
open Real

section Chap1

#print Rat
-- I don't wnat to tyype ℚ
example : forall r : Rat, r^2 ≠ 2 := by
  intros r h
  -- Reason to use set vs let?
  set p := r.num
  set q := r.den
  -- have hpq := exists p q, r = p / q
  have hr : r = p/q := by exact Eq.symm (Rat.num_div_den r)
  have : q ≠ 0 := by exact r.den_nz
  have : ((p : Rat) / q)^2 = 2 := by rw [<- hr]; exact h
  have : p^2 = 2*q^2 := by qify; field_simp at *; linarith
  -- What now?
  sorry
  --have : Even p := by
  --  have Even (p ^ 2) := by exact?

  -- why is this such an awful proof shouldn't some automation find it?
  -- Or have I been going about tnis the wrong way?

  /-
  have : p ^2 = 2 * q ^ 2 := by grind
  have : Even (p ^ 2) := by grind
  have : Even p := by grind
  obtain (w, hw) := exists w, p = 2*w := by grind
  --have : exists w, p = 2 * w
  have : q ^ 2 = 2 * w ^ 2
  have : even q
  -- ? p and q in lowest form?
-/

#check irrational_sqrt_two
#norm_num sqrt 9

#check {r : Rat // r^2 < 2} -- subtype
#check {r : Rat | r ^ 2 < 2}  -- set
#reduce Set Rat
example : Set Rat = (Rat -> Prop) := rfl
#check rfl
end Chap1
