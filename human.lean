module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import ai
open Real
variable (ε δ : ℝ)

theorem sqr_ge_zero : forall x : ℝ, x^2 >= 0 := proof1

theorem sin_bound : forall x, sin x >= -1 := proof2

/-
namespace integ

variable (rho : Real -> Real)
variable (rho_norm : ∫ x in -inf...inf rho x = 1)


def exp_x := ∫ rho x
def exp f := ∫ (rho x) * (f x)

end integ
-/

namespace rock
variable (h : Real) (hpos : h > 0)
include hpos


/-
Sohuld I have fonruate this idfferently using some subset type?
-/
noncomputable def rho x :=
    if 0 <= x /\ x <= h
    then
        1 / (2 * (sqrt (h * x)))
    else 0

theorem rho_norm : ∫ x in 0..h, rho h x = 1 := proof3 hpos

theorem rho_norm2 : ∫ x in 0..h, rho h x = 1 := by
    calc
        _ =  ∫ x in 0..h, (1 / (2 * (sqrt (h * x)))) := proof4
        _ = 1 / (2 * (sqrt h)) * ∫ x in 0..h, (x ^ (-1/2 : Real)) := proof5
        _ = 2 / (2 * (sqrt h)) * (h  ^ (1/2 : Real)) := proof6
        _ = 1 := proof7




end rock
