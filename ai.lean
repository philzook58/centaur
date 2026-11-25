module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

public section

export Real (sin)

theorem proof1 : ∀ x : ℝ, x ^ 2 ≥ 0 := by
  intro x
  exact sq_nonneg x

theorem proof2 : ∀ x : ℝ, sin x ≥ -1 := by
  intro x
  exact Real.neg_one_le_sin x

theorem proof4 {h : ℝ}
    (hh : 0 ≤ h := by first | assumption | exact le_of_lt (by assumption)) :
    (∫ x in (0 : ℝ)..h,
      if 0 ≤ x ∧ x ≤ h then 1 / (2 * Real.sqrt (h * x)) else 0) =
      ∫ x in (0 : ℝ)..h, 1 / (2 * Real.sqrt (h * x)) := by
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hh] at hx
  exact ite_eq_left (show 0 ≤ x ∧ x ≤ h from hx)

theorem proof5 {h : ℝ}
    (hh : 0 ≤ h := by first | assumption | exact le_of_lt (by assumption)) :
    (∫ x in (0 : ℝ)..h, 1 / (2 * Real.sqrt (h * x))) =
      (1 / (2 * Real.sqrt h)) * ∫ x in (0 : ℝ)..h, x ^ (-1 / 2 : ℝ) := by
  rw [neg_div]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hh] at hx
  dsimp only
  rw [Real.sqrt_mul hh, Real.rpow_neg hx.1, ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem proof6 {h : ℝ} :
    ((1 / (2 * Real.sqrt h)) * ∫ x in (0 : ℝ)..h, x ^ (-1 / 2 : ℝ)) =
      (2 / (2 * Real.sqrt h)) * h ^ (1 / 2 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem proof7 {h : ℝ} (hh : 0 < h := by assumption) :
    (2 / (2 * Real.sqrt h)) * h ^ (1 / 2 : ℝ) = 1 := by
  have hs : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  rw [← Real.sqrt_eq_rpow]
  field_simp

theorem proof3 {h : ℝ} (hh : 0 < h := by assumption) :
    (∫ x in (0 : ℝ)..h,
      if 0 ≤ x ∧ x ≤ h then 1 / (2 * Real.sqrt (h * x)) else 0) = 1 := by
  have hs : Real.sqrt h ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hh)
  calc
    _ = ∫ x in (0 : ℝ)..h, (1 / (2 * Real.sqrt h)) * x ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hh.le] at hx
      change 0 ≤ x ∧ x ≤ h at hx
      dsimp only
      rw [ite_eq_left hx, Real.sqrt_mul hh.le, Real.rpow_neg hx.1, ← Real.sqrt_eq_rpow]
      simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
      ring
    _ = (1 / (2 * Real.sqrt h)) *
        ((h ^ ((-(1 / 2 : ℝ)) + 1) - (0 : ℝ) ^ ((-(1 / 2 : ℝ)) + 1)) /
          ((-(1 / 2 : ℝ)) + 1)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    _ = 1 := by
      norm_num
      rw [← Real.sqrt_eq_rpow]
      field_simp
