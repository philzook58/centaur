module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace FourierAI

-- Specialize mathlib's Gaussian integral to b = 1 and t = -ω, then express
-- the complex square root of π as the positive real square root.
theorem gaussian_integral (ω : ℝ) :
    (∫ t : ℝ, (Real.exp (-(t ^ 2)) : ℂ) * Complex.exp (-Complex.I * ω * t)) =
      (Real.sqrt Real.pi : ℂ) * Complex.exp (-(ω : ℂ) ^ 2 / 4) := by
  have h := fourierIntegral_gaussian (b := 1) (by norm_num) (-(ω : ℂ))
  have hs : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  rw [hs]
  simpa only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    neg_mul, mul_neg, mul_comm, neg_one_mul, div_one, neg_sq, mul_one, one_mul] using h

theorem proof1 :
    (fun ω : ℝ ↦ ∫ t : ℝ,
      (Real.exp (-(t ^ 2)) : ℂ) * Complex.exp (-Complex.I * ω * t)) =
    (fun ω : ℝ ↦ ((Real.sqrt Real.pi * Real.exp (-(ω ^ 2) / 4) : ℝ) : ℂ)) := by
  funext ω
  simpa only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat] using gaussian_integral ω

theorem proof1_complex :
    (fun ω : ℝ ↦ ∫ t : ℝ,
      Complex.exp (-(t : ℂ) ^ 2) * Complex.exp (-Complex.I * ω * t)) =
    (fun ω : ℝ ↦ (Real.sqrt Real.pi : ℂ) * Complex.exp (-(ω : ℂ) ^ 2 / 4)) := by
  funext ω
  simpa only [Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow] using gaussian_integral ω

namespace trans_gauss

noncomputable def formula (ω : ℝ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp (-(ω : ℂ) ^ 2 / 4)

theorem correct :
    (fun ω : ℝ ↦ ∫ t : ℝ,
      Complex.exp (-(t : ℂ) ^ 2) * Complex.exp (-Complex.I * ω * t)) = formula :=
  proof1_complex

end trans_gauss

noncomputable def trans_gauss :
    {f : ℝ → ℂ // (fun ω : ℝ ↦ ∫ t : ℝ,
      Complex.exp (-(t : ℂ) ^ 2) * Complex.exp (-Complex.I * ω * t)) = f} :=
  ⟨trans_gauss.formula, trans_gauss.correct⟩

namespace trans_gauss2

noncomputable def formula (ξ : ℝ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) * Complex.exp (-(Real.pi : ℂ) ^ 2 * (ξ : ℂ) ^ 2)

-- Mathlib's frequency ξ corresponds to angular frequency 2πξ.
theorem correct : 𝓕 (fun t : ℝ ↦ Complex.exp (-(t : ℂ) ^ 2)) = formula := by
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  calc
    _ = ∫ t : ℝ, (Real.exp (-(t ^ 2)) : ℂ) *
        Complex.exp (-Complex.I * (2 * Real.pi * ξ : ℝ) * t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [Complex.ofReal_exp]
      push_cast
      rw [mul_comm]
      congr 1
      congr 1
      ring
    _ = _ := gaussian_integral (2 * Real.pi * ξ)
    _ = formula ξ := by
      unfold formula
      congr 2
      push_cast
      ring

end trans_gauss2

noncomputable def trans_gauss2 :
    {f : ℝ → ℂ // 𝓕 (fun t : ℝ ↦ Complex.exp (-(t : ℂ) ^ 2)) = f} :=
  ⟨trans_gauss2.formula, trans_gauss2.correct⟩

end FourierAI
