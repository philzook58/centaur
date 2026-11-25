module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.Tactic

/-!
# AI-owned answers to the SymPy tutorial requests

Source: https://docs.sympy.org/latest/tutorials/intro-tutorial/index.html

`sympyhuman.lean` owns the questions; this file owns the chosen expressions and their proofs.
Every answer is a named term. There is no AI tactic, custom syntax, or running watcher here.
For equality requests, `.val` is the answer and `.property` certifies input = answer.
The public answers below use implicit parameters inferred from the human request's type.
Each answer also has `.formula` (inspectable data) and `.correct` (its certificate).
`Checked` retains the underlying proofs; the public interface packages those proofs with formulas.
Parameters absent from the requested property, such as the ODE constants, remain explicit.
-/

@[expose] public section

namespace SympyAI.Checked

open Real Filter MeasureTheory
open scoped Topology Matrix

noncomputable section

-- Introduction and basic operations.

def simplifyRadical : { y : ℝ // Real.sqrt 8 = y } :=
  ⟨2 * Real.sqrt 2, by
    rw [show (8 : ℝ) = 4 * 2 by norm_num, Real.sqrt_mul (by norm_num)]
    norm_num⟩

def substituteCos (y : ℝ) : { z : ℝ // (fun x ↦ Real.cos x + 1) y = z } :=
  ⟨Real.cos y + 1, rfl⟩

def substituteAtZero : { y : ℝ // Real.cos 0 + 1 = y } := ⟨2, by norm_num⟩

def substitutePower (x : ℝ) : { y : ℝ // x ^ 3 + 4 * x ^ 2 + 6 * x + 10 = y } :=
  ⟨x ^ 3 + 4 * x ^ 2 + 6 * x + 10, rfl⟩

def exactRational : { y : ℚ // (1 / 3 : ℚ) + 1 / 6 = y } := ⟨1 / 2, by norm_num⟩

/-- A rational answer with an absolute error certificate, rather than an unchecked decimal. -/
def sqrtTwoApprox : { q : ℚ // |Real.sqrt 2 - (q : ℝ)| ≤ 1 / 1000 } :=
  ⟨1414 / 1000, by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hp := Real.sqrt_nonneg (2 : ℝ)
    norm_num
    rw [abs_le]
    constructor <;> nlinarith⟩

-- Polynomial and rational simplification.

def simplifyTrig (x : ℝ) : { y : ℝ // Real.sin x ^ 2 + Real.cos x ^ 2 = y } :=
  ⟨1, Real.sin_sq_add_cos_sq x⟩

def simplifyRational (x : ℝ) (hx : x + 1 ≠ 0 := by assumption) :
    { y : ℝ // (x ^ 3 + x ^ 2 - x - 1) / (x ^ 2 + 2 * x + 1) = y } :=
  ⟨x - 1, by
    have hd : x ^ 2 + 2 * x + 1 ≠ 0 := by nlinarith [sq_pos_of_ne_zero hx]
    apply (div_eq_iff hd).2
    ring⟩

namespace expandSquare

/-- The selected formula, kept separate so `#print` displays only the mathematical answer. -/
def formula (x : ℝ) : ℝ := x ^ 2 + 2 * x + 1

/-- The certificate for the formula; the human file need not repeat this statement. -/
theorem correct (x : ℝ) : (x + 1) ^ 2 = formula x := by
  unfold formula
  ring

end expandSquare

def expandSquare (x : ℝ) : { y : ℝ // (x + 1) ^ 2 = y } :=
  ⟨expandSquare.formula x, expandSquare.correct x⟩

def expandProduct (x : ℝ) : { y : ℝ // (x + 2) * (x - 3) = y } :=
  ⟨x ^ 2 - x - 6, by ring⟩

def expandAndCancel (x : ℝ) : { y : ℝ // (x + 1) * (x - 2) - (x - 1) * x = y } :=
  ⟨-2, by ring⟩

def factorCubic (x : ℝ) : { y : ℝ // x ^ 3 - x ^ 2 + x - 1 = y } :=
  ⟨(x - 1) * (x ^ 2 + 1), by ring⟩

def factorMultivariate (x y z : ℝ) :
    { w : ℝ // x ^ 2 * z + 4 * x * y * z + 4 * y ^ 2 * z = w } :=
  ⟨z * (x + 2 * y) ^ 2, by ring⟩

def collectPowers (x y z : ℝ) :
    { w : ℝ // x * y + x - 3 + 2 * x ^ 2 - z * x ^ 2 + x ^ 3 = w } :=
  ⟨x ^ 3 + (2 - z) * x ^ 2 + (y + 1) * x - 3, by ring⟩

/-- Coefficients are meaningful for polynomials, not just their values at one point. -/
def quadraticCoefficient (y z : ℝ) :
    { c : ℝ //
      (Polynomial.X ^ 3 + Polynomial.C (2 - z) * Polynomial.X ^ 2 +
        Polynomial.C (y + 1) * Polynomial.X - Polynomial.C 3).coeff 2 = c } :=
  ⟨2 - z, by
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    norm_num⟩

def cancelRational (x : ℝ) (hx : x ≠ 0 := by assumption)
    (hx1 : x + 1 ≠ 0 := by assumption) :
    { y : ℝ // (x ^ 2 + 2 * x + 1) / (x ^ 2 + x) = y } :=
  ⟨(x + 1) / x, by
    have hd : x ^ 2 + x ≠ 0 := by
      simpa only [mul_add, mul_one, ← pow_two] using mul_ne_zero hx hx1
    apply (div_eq_iff hd).2
    field_simp
    ring⟩

def partialFractions (x : ℝ) (hx : x ≠ 0 := by assumption)
    (hx4 : x + 4 ≠ 0 := by assumption) :
    { y : ℝ //
      (4 * x ^ 3 + 21 * x ^ 2 + 10 * x + 12) /
        (x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x) = y } :=
  ⟨(2 * x - 1) / (x ^ 2 + x + 1) - 1 / (x + 4) + 3 / x, by
    have hq : x ^ 2 + x + 1 ≠ 0 := by nlinarith [sq_nonneg (x + 1 / 2)]
    have hd : x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x ≠ 0 := by
      have hf : x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x =
          x * (x + 4) * (x ^ 2 + x + 1) := by ring
      rw [hf]
      exact mul_ne_zero (mul_ne_zero hx hx4) hq
    apply (div_eq_iff hd).2
    have hq' : 1 + x + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg (x + 1 / 2)]
    field_simp [hq, hq']
    ring_nf
    field_simp [hq']
    ring⟩

-- Trigonometric identities, powers, and logarithms.

def expandTrig (x y : ℝ) : { z : ℝ // Real.sin (x + y) = z } :=
  ⟨Real.sin x * Real.cos y + Real.sin y * Real.cos x, by rw [Real.sin_add]; ring⟩

def combineTrig (x y : ℝ) :
    { z : ℝ // Real.sin x * Real.cos y + Real.sin y * Real.cos x = z } :=
  ⟨Real.sin (x + y), by rw [Real.sin_add]; ring⟩

def simplifyHyperbolic (x : ℝ) : { y : ℝ // Real.cosh x ^ 2 + Real.sinh x ^ 2 = y } :=
  ⟨Real.cosh (2 * x), (Real.cosh_two_mul x).symm⟩

def combinePowers (x a b : ℝ) (hx : 0 < x := by assumption) :
    { y : ℝ // x ^ a * x ^ b = y } := ⟨x ^ (a + b), (Real.rpow_add hx a b).symm⟩

def expandPowerBase (x y a : ℝ) (hx : 0 ≤ x := by assumption)
    (hy : 0 ≤ y := by assumption) : { z : ℝ // (x * y) ^ a = z } :=
  ⟨x ^ a * y ^ a, Real.mul_rpow hx hy⟩

def denestPower (x a b : ℝ) (hx : 0 ≤ x := by assumption) :
    { y : ℝ // (x ^ a) ^ b = y } := ⟨x ^ (a * b), (Real.rpow_mul hx a b).symm⟩

def expandLog (x y : ℝ) (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    { z : ℝ // Real.log (x * y) = z } :=
  ⟨Real.log x + Real.log y, Real.log_mul hx.ne' hy.ne'⟩

def combineLog (x y : ℝ) (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    { z : ℝ // Real.log x + Real.log y = z } :=
  ⟨Real.log (x * y), (Real.log_mul hx.ne' hy.ne').symm⟩

def expandLogPower (x a : ℝ) (hx : 0 < x := by assumption) :
    { y : ℝ // Real.log (x ^ a) = y } := ⟨a * Real.log x, Real.log_rpow hx a⟩

def simplifySqrtSquare (x : ℝ) : { y : ℝ // Real.sqrt (x ^ 2) = y } :=
  ⟨|x|, Real.sqrt_sq_eq_abs x⟩

-- Special functions and continued fractions.

def rewriteFactorial (n : ℕ) : { y : ℝ // (n.factorial : ℝ) = y } :=
  ⟨Real.Gamma (n + 1), (Real.Gamma_nat_eq_factorial n).symm⟩

def expandGamma (x : ℝ) (hx : 0 < x := by assumption) :
    { y : ℝ // Real.Gamma (x + 3) = y } :=
  ⟨x * (x + 1) * (x + 2) * Real.Gamma x, by
    rw [show x + 3 = (x + 1) + 1 + 1 by ring,
      Real.Gamma_add_one (by linarith : x + 1 + 1 ≠ 0),
      Real.Gamma_add_one (by linarith : x + 1 ≠ 0), Real.Gamma_add_one hx.ne']
    ring⟩

def simplifyGammaRatio (x : ℝ) (hx : 2 < x := by assumption) :
    { y : ℝ // Real.Gamma x / Real.Gamma (x - 2) = y } :=
  ⟨(x - 2) * (x - 1), by
    have hg : Real.Gamma (x - 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    conv_lhs => arg 1; rw [show x = (x - 2) + 1 + 1 by ring]
    rw [Real.Gamma_add_one (by linarith : x - 2 + 1 ≠ 0),
      Real.Gamma_add_one (by linarith : x - 2 ≠ 0)]
    field_simp
    ring⟩

def simplifyGammaReflection (x : ℝ) :
    { y : ℝ // Real.Gamma x * Real.Gamma (1 - x) = y } :=
  ⟨Real.pi / Real.sin (Real.pi * x), Real.Gamma_mul_Gamma_one_sub x⟩

/-- Reindexing n as n+3 makes the factorial domain condition explicit. -/
def simplifyFactorialRatio (n : ℕ) :
    { y : ℚ // ((n + 3).factorial : ℚ) / n.factorial = y } :=
  ⟨(n + 3) * (n + 2) * (n + 1), by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring⟩

def continuedFraction : { y : ℚ // (1 + 1 / (2 + 1 / (3 + 1 / 4)) : ℚ) = y } :=
  ⟨43 / 30, by norm_num⟩

-- Calculus: the answer functions come with actual derivative certificates.

def differentiateCos : { g : ℝ → ℝ // ∀ x, HasDerivAt Real.cos (g x) x } :=
  ⟨fun x ↦ -Real.sin x, Real.hasDerivAt_cos⟩

def differentiateExpSquare :
    { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t ^ 2)) (g x) x } :=
  ⟨fun x ↦ 2 * x * Real.exp (x ^ 2), by
    intro x
    convert (Real.hasDerivAt_exp (x ^ 2)).comp x (hasDerivAt_pow 2 x) using 1
    · rfl
    · ring⟩

def thirdDerivative : { g : ℝ → ℝ // ∀ x, iteratedDeriv 3 (fun t : ℝ ↦ t ^ 4) x = g x } :=
  ⟨fun x ↦ 24 * x, by
    intro x
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    have h1 : deriv (fun t : ℝ ↦ t ^ 4) = fun t ↦ 4 * t ^ 3 := by
      funext t
      simp
    have h2 : deriv (fun t : ℝ ↦ 4 * t ^ 3) = fun t ↦ 12 * t ^ 2 := by
      funext t
      convert ((hasDerivAt_pow 3 t).const_mul 4).deriv using 1
      ring
    rw [h1, h2]
    convert ((hasDerivAt_pow 2 x).const_mul 12).deriv using 1
    ring⟩

def partialDerivative (y z : ℝ) :
    { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t * y * z)) (g x) x } :=
  ⟨fun x ↦ y * z * Real.exp (x * y * z), by
    intro x
    convert (Real.hasDerivAt_exp (x * y * z)).comp x
      (((hasDerivAt_id x).mul_const y).mul_const z) using 1
    · rfl
    · ring⟩

def antiderivativeCos : { F : ℝ → ℝ // ∀ x, HasDerivAt F (Real.cos x) x } :=
  ⟨Real.sin, Real.hasDerivAt_sin⟩

def antiderivativeLogSquare :
    { F : ℝ → ℝ // ∀ x, 0 < x → HasDerivAt F (Real.log x ^ 2) x } :=
  ⟨fun x ↦ x * Real.log x ^ 2 - 2 * x * Real.log x + 2 * x, by
    intro x hx
    convert (((hasDerivAt_id x).mul ((Real.hasDerivAt_log hx.ne').pow 2)).sub
      (((hasDerivAt_id x).const_mul 2).mul (Real.hasDerivAt_log hx.ne'))).add
      ((hasDerivAt_id x).const_mul 2) using 1
    · rfl
    · dsimp
      field_simp
      ring⟩

def integratePower : { y : ℝ // (∫ x : ℝ in 0..1, x ^ 2) = y } :=
  ⟨1 / 3, by rw [integral_pow]; norm_num⟩

def integrateCos (a b : ℝ) : { y : ℝ // (∫ x : ℝ in a..b, Real.cos x) = y } :=
  ⟨Real.sin b - Real.sin a, integral_cos⟩

def integrateExponentialTail : { y : ℝ // (∫ x : ℝ in Set.Ioi 0, Real.exp (-x)) = y } :=
  ⟨1, integral_exp_neg_Ioi_zero⟩

def integrateGaussian : { y : ℝ // (∫ x : ℝ, Real.exp (-(x ^ 2))) = y } :=
  ⟨Real.sqrt Real.pi, by simpa using integral_gaussian (1 : ℝ)⟩

def numericIntegral :
    { q : ℚ // |(∫ x : ℝ in 0..1, Real.sqrt 2 * x) - (q : ℝ)| ≤ 1 / 1000 } :=
  ⟨707 / 1000, by
    rw [intervalIntegral.integral_const_mul, integral_id]
    have hs := sqrtTwoApprox.property
    change |Real.sqrt 2 - ((1414 / 1000 : ℚ) : ℝ)| ≤ 1 / 1000 at hs
    norm_num at hs ⊢
    rw [abs_le] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]⟩

def limitSinc : { y : ℝ // Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 y) } :=
  ⟨1, Real.tendsto_sin_div_nhdsNE_zero⟩

def limitPolynomialOverExp :
    { y : ℝ // Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp x) atTop (𝓝 y) } :=
  ⟨0, by simpa [div_eq_mul_inv, Real.exp_neg] using
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2⟩

theorem reciprocalRightLimit : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop := by
  simpa only [one_div] using (tendsto_inv_nhdsGT_zero :
    Tendsto (fun x : ℝ ↦ x⁻¹) (𝓝[>] 0) atTop)

/-- A series answer includes a remainder assertion, not a false exact equality. -/
def expSeries :
    { p : ℝ → ℝ // (fun x ↦ Real.exp x - p x) =O[𝓝 (0 : ℝ)] (fun x ↦ x ^ 4) } :=
  ⟨fun x ↦ 1 + x + x ^ 2 / 2 + x ^ 3 / 6, by
    simpa [Finset.sum_range_succ, Nat.factorial, add_assoc] using
      Real.exp_sub_sum_range_isBigO_pow 4⟩

/-- The centered finite difference is exact on quadratics, for nonzero step size. -/
def finiteDifference (x h : ℝ) (hh : h ≠ 0 := by assumption) :
    { y : ℝ // ((x + h) ^ 2 - (x - h) ^ 2) / (2 * h) = y } :=
  ⟨2 * x, by field_simp; ring⟩

-- Solvers: the equivalences establish completeness, not just membership of one root.

def solveSquare : { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 = 1 } :=
  ⟨{-1, 1}, by
    intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl) <;> norm_num
    · intro hx
      have hf : (x - 1) * (x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · right; linarith
      · left; linarith⟩

def solveQuadratic : { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 - x = 0 } :=
  ⟨{0, 1}, by
    intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl) <;> norm_num
    · intro hx
      have hf : x * (x - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · exact Or.inl h
      · right; linarith⟩

def solveIdentity : { S : Set ℝ // ∀ x, x ∈ S ↔ x - x = 0 } :=
  ⟨Set.univ, by simp⟩

def solveExponential : { S : Set ℝ // ∀ x, x ∈ S ↔ Real.exp x = 0 } :=
  ⟨∅, by simp [Real.exp_ne_zero]⟩

def solveLinearSystem :
    { S : Set (ℝ × ℝ × ℝ) // ∀ x y z,
      (x, y, z) ∈ S ↔ x + y + z = 1 ∧ x + y + 2 * z = 3 } :=
  ⟨{p | p.1 = -p.2.1 - 1 ∧ p.2.2 = 2}, by
    intro x y z
    change (x = -y - 1 ∧ z = 2) ↔ _
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith⟩

def solveNonlinearSystem :
    { S : Set (ℝ × ℝ) // ∀ x y, (x, y) ∈ S ↔ x * y = 1 ∧ x = 2 } :=
  ⟨{(2, 1 / 2)}, by
    intro x y
    simp only [Set.mem_singleton_iff, Prod.mk.injEq]
    constructor <;> rintro ⟨h1, h2⟩
    · subst x; subst y; norm_num
    · constructor <;> nlinarith⟩

/-- A certified two-parameter solution family; this does not assert ODE completeness. -/
def solveODE (c₁ c₂ : ℝ) :
    { f : ℝ → ℝ // ∀ x, deriv (deriv f) x - 2 * deriv f x + f x = Real.sin x } := by
  let f := fun x ↦ (c₁ + c₂ * x) * Real.exp x + Real.cos x / 2
  let g := fun x ↦ (c₂ + (c₁ + c₂ * x)) * Real.exp x - Real.sin x / 2
  let k := fun x ↦ (2 * c₂ + (c₁ + c₂ * x)) * Real.exp x - Real.cos x / 2
  have hf : ∀ x, HasDerivAt f (g x) x := by
    intro x
    convert ((((hasDerivAt_const x c₁).add ((hasDerivAt_id x).const_mul c₂)).mul
      (Real.hasDerivAt_exp x)).add ((Real.hasDerivAt_cos x).div_const 2)) using 1
    · rfl
    · dsimp [g]
      ring
  have hg : ∀ x, HasDerivAt g (k x) x := by
    intro x
    convert ((((hasDerivAt_const x c₂).add ((hasDerivAt_const x c₁).add
      ((hasDerivAt_id x).const_mul c₂))).mul (Real.hasDerivAt_exp x)).sub
      ((Real.hasDerivAt_sin x).div_const 2)) using 1
    · rfl
    · dsimp [k]
      ring
  refine ⟨f, fun x ↦ ?_⟩
  have he : deriv f = g := funext fun t ↦ (hf t).deriv
  rw [he, (hg x).deriv]
  dsimp [f, g, k]
  ring

-- Matrices: exact rational entries make the answers executable as well as checkable.

def matrixAdd :
    { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] + !![0, 3; 0, 7] = A } :=
  ⟨!![1, 6; -2, 10], by ext i j; fin_cases i <;> fin_cases j <;> norm_num⟩

def matrixMultiply :
    { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] * !![0, 3; 0, 7] = A } :=
  ⟨!![0, 24; 0, 15], by norm_num [Matrix.mul_fin_two]⟩

def matrixVectorProduct :
    { v : Fin 2 → ℚ // (!![1, 2, 3; 3, 2, 1] : Matrix (Fin 2) (Fin 3) ℚ) *ᵥ
      ![0, 1, 1] = v } :=
  ⟨![5, 3], by ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]⟩

def matrixTranspose :
    { A : Matrix (Fin 3) (Fin 2) ℚ // (!![1, 2, 3; 4, 5, 6] :
      Matrix (Fin 2) (Fin 3) ℚ).transpose = A } := ⟨!![1, 4; 2, 5; 3, 6], by decide⟩

def matrixDeterminant :
    { d : ℚ // (!![1, 0, 1; 2, -1, 3; 4, 3, 2] : Matrix (Fin 3) (Fin 3) ℚ).det = d } :=
  ⟨-1, by norm_num [Matrix.det_fin_three]⟩

def matrixInverse :
    { B : Matrix (Fin 2) (Fin 2) ℚ //
      (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) * B = 1 ∧
      B * (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) = 1 } :=
  ⟨!![1 / 3, -1 / 3; 2 / 9, 1 / 9], by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_fin_two]⟩

/-- A nullspace parametrization, proving that every kernel vector is represented. -/
def matrixNullspace :
    { v : ℚ → ℚ → ℚ → (Fin 5 → ℚ) // ∀ w : Fin 5 → ℚ,
      (!![1, 2, 3, 0, 0; 4, 10, 0, 0, 1] : Matrix (Fin 2) (Fin 5) ℚ) *ᵥ w = 0 ↔
        ∃ a b c, w = v a b c } := by
  refine ⟨fun a b c ↦ ![-15 * a + c, 6 * a - c / 2, a, b, c], ?_⟩
  intro w
  constructor
  · intro hw
    have h0 := congrFun hw 0
    have h1 := congrFun hw 1
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    refine ⟨w 2, w 3, w 4, ?_⟩
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro ⟨a, b, c, rfl⟩
    ext i
    fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The returned columns span the image and give unique coordinates in that image. -/
def matrixColumnspace :
    { b : Fin 2 → Fin 3 → ℚ //
      (∀ w : Fin 3 → ℚ,
        (∃ v, (!![1, 1, 2; 2, 1, 3; 3, 1, 4] : Matrix (Fin 3) (Fin 3) ℚ) *ᵥ v = w) ↔
          ∃ a c : ℚ, w = a • b 0 + c • b 1) ∧
      Function.Injective (fun c : Fin 2 → ℚ ↦ c 0 • b 0 + c 1 • b 1) } := by
  refine ⟨![![1, 2, 3], ![1, 1, 1]], ?_, ?_⟩
  · intro w
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v 0 + v 2, v 1 + v 2, ?_⟩
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
    · rintro ⟨a, c, rfl⟩
      refine ⟨![a, c, 0], ?_⟩
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mul_comm]
  · intro u v huv
    have h0 := congrFun huv 0
    have h1 := congrFun huv 1
    norm_num at h0 h1
    ext i
    fin_cases i <;> norm_num <;> linarith

/-- Reduced row echelon form with an invertible row-operation certificate. -/
structure RowReduction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) where
  reduced : Matrix (Fin m) (Fin n) ℚ
  operations : Matrix (Fin m) (Fin m) ℚ
  invertible_operations : IsUnit operations.det
  correct : operations * A = reduced
  reduced_form : reduced.IsReducedRowEchelon

def matrixRref : RowReduction
    (!![1, 0, 1, 3; 2, 3, 4, 7; -1, -3, -3, -4] : Matrix (Fin 3) (Fin 4) ℚ) where
  reduced := !![1, 0, 1, 3; 0, 1, 2 / 3, 1 / 3; 0, 0, 0, 0]
  operations := !![1, 0, 0; -2 / 3, 1 / 3, 0; -1, 1, 1]
  invertible_operations := by norm_num [Matrix.det_fin_three]
  correct := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  reduced_form := by
    constructor
    · norm_num [Matrix.IsRowEchelon, Fin.forall_fin_succ]
    · intro i c hc
      fin_cases i <;> fin_cases c <;>
        simp_all [Matrix.IsLeadingEntry, Fin.forall_fin_succ]
    · intro i j c hij hc
      fin_cases i <;> fin_cases j <;> fin_cases c <;>
        simp_all [Matrix.IsLeadingEntry, Fin.forall_fin_succ]

/-- An explicit basis and inverse certify a diagonalization and its eigenvalues. -/
structure Diagonalization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) where
  eigenvalues : Fin n → ℚ
  basis : Matrix (Fin n) (Fin n) ℚ
  inverse : Matrix (Fin n) (Fin n) ℚ
  basis_mul_inverse : basis * inverse = 1
  inverse_mul_basis : inverse * basis = 1
  eigenvectors : A * basis = basis * Matrix.diagonal eigenvalues

def matrixDiagonalization : Diagonalization
    (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
      Matrix (Fin 4) (Fin 4) ℚ) where
  eigenvalues := ![-2, 3, 5, 5]
  basis := !![0, 1, 1, 0; 1, 1, 1, -1; 1, 1, 1, 0; 1, 1, 0, 1]
  inverse := !![-1, 0, 1, 0; 1, 1, -2, 1; 0, -1, 2, -1; 0, -1, 1, 0]
  basis_mul_inverse := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  inverse_mul_basis := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]
  eigenvectors := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

def matrixCharacteristicPolynomial :
    { p : Polynomial ℚ //
      (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
        Matrix (Fin 4) (Fin 4) ℚ).charpoly = p } := by
  let d := matrixDiagonalization
  refine ⟨(Polynomial.X + 2) * (Polynomial.X - 3) * (Polynomial.X - 5) ^ 2, ?_⟩
  have he : (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
      Matrix (Fin 4) (Fin 4) ℚ) = d.basis * Matrix.diagonal d.eigenvalues * d.inverse := by
    rw [← d.eigenvectors, Matrix.mul_assoc, d.basis_mul_inverse, Matrix.mul_one]
  rw [he, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, d.inverse_mul_basis, Matrix.one_mul,
    Matrix.charpoly_diagonal]
  norm_num [d, matrixDiagonalization, Fin.prod_univ_succ, Polynomial.C_ofNat]
  ring

-- Expression manipulation is function application and certified rewriting in Lean.

def rewriteSubexpression (x y : ℝ) :
    { z : ℝ // x ^ 2 + x * (y + 1) = z } := ⟨x * (x + y + 1), by ring⟩

def delayedExpression (x : ℝ) : { y : ℝ // (fun t : ℝ ↦ (t + 1) ^ 2) x = y } :=
  expandSquare x

end

end SympyAI.Checked

namespace SympyAI

open Real Filter MeasureTheory
open scoped Topology Matrix

noncomputable section

-- Public request names and their separately inspectable formulas and certificates.

namespace simplifyRadical

def formula : ℝ :=
  2 * Real.sqrt 2

theorem correct :
    Real.sqrt 8 = (formula) :=
  (Checked.simplifyRadical).property

end simplifyRadical

def simplifyRadical :
    { y : ℝ // Real.sqrt 8 = y } :=
  ⟨simplifyRadical.formula, simplifyRadical.correct⟩

namespace substituteCos

def formula (y : ℝ) : ℝ :=
  Real.cos y + 1

theorem correct (y : ℝ) :
    (fun x ↦ Real.cos x + 1) y = (formula y) :=
  (Checked.substituteCos y).property

end substituteCos

def substituteCos {y : ℝ} :
    { z : ℝ // (fun x ↦ Real.cos x + 1) y = z } :=
  ⟨substituteCos.formula y, substituteCos.correct y⟩

namespace substituteAtZero

def formula : ℝ :=
  2

theorem correct :
    Real.cos 0 + 1 = (formula) :=
  (Checked.substituteAtZero).property

end substituteAtZero

def substituteAtZero :
    { y : ℝ // Real.cos 0 + 1 = y } :=
  ⟨substituteAtZero.formula, substituteAtZero.correct⟩

namespace substitutePower

def formula (x : ℝ) : ℝ :=
  x ^ 3 + 4 * x ^ 2 + 6 * x + 10

theorem correct (x : ℝ) :
    x ^ 3 + 4 * x ^ 2 + 6 * x + 10 = (formula x) :=
  (Checked.substitutePower x).property

end substitutePower

def substitutePower {x : ℝ} :
    { y : ℝ // x ^ 3 + 4 * x ^ 2 + 6 * x + 10 = y } :=
  ⟨substitutePower.formula x, substitutePower.correct x⟩

namespace exactRational

def formula : ℚ :=
  1 / 2

theorem correct :
    (1 / 3 : ℚ) + 1 / 6 = (formula) :=
  (Checked.exactRational).property

end exactRational

def exactRational :
    { y : ℚ // (1 / 3 : ℚ) + 1 / 6 = y } :=
  ⟨exactRational.formula, exactRational.correct⟩

namespace sqrtTwoApprox

def formula : ℚ :=
  1414 / 1000

theorem correct :
    |Real.sqrt 2 - ((formula) : ℝ)| ≤ 1 / 1000 :=
  (Checked.sqrtTwoApprox).property

end sqrtTwoApprox

def sqrtTwoApprox :
    { q : ℚ // |Real.sqrt 2 - (q : ℝ)| ≤ 1 / 1000 } :=
  ⟨sqrtTwoApprox.formula, sqrtTwoApprox.correct⟩

namespace simplifyTrig

def formula : ℝ :=
  1

theorem correct (x : ℝ) :
    Real.sin x ^ 2 + Real.cos x ^ 2 = (formula) :=
  (Checked.simplifyTrig x).property

end simplifyTrig

def simplifyTrig {x : ℝ} :
    { y : ℝ // Real.sin x ^ 2 + Real.cos x ^ 2 = y } :=
  ⟨simplifyTrig.formula, simplifyTrig.correct x⟩

namespace simplifyRational

def formula (x : ℝ) : ℝ :=
  x - 1

theorem correct (x : ℝ) (hx : x + 1 ≠ 0 := by assumption) :
    (x ^ 3 + x ^ 2 - x - 1) / (x ^ 2 + 2 * x + 1) = (formula x) :=
  (Checked.simplifyRational x hx).property

end simplifyRational

def simplifyRational {x : ℝ} (hx : x + 1 ≠ 0 := by assumption) :
    { y : ℝ // (x ^ 3 + x ^ 2 - x - 1) / (x ^ 2 + 2 * x + 1) = y } :=
  ⟨simplifyRational.formula x, simplifyRational.correct x hx⟩

namespace expandSquare

def formula (x : ℝ) : ℝ :=
  x ^ 2 + 2 * x + 1

theorem correct (x : ℝ) :
    (x + 1) ^ 2 = (formula x) :=
  (Checked.expandSquare x).property

end expandSquare

def expandSquare {x : ℝ} :
    { y : ℝ // (x + 1) ^ 2 = y } :=
  ⟨expandSquare.formula x, expandSquare.correct x⟩

namespace expandProduct

def formula (x : ℝ) : ℝ :=
  x ^ 2 - x - 6

theorem correct (x : ℝ) :
    (x + 2) * (x - 3) = (formula x) :=
  (Checked.expandProduct x).property

end expandProduct

def expandProduct {x : ℝ} :
    { y : ℝ // (x + 2) * (x - 3) = y } :=
  ⟨expandProduct.formula x, expandProduct.correct x⟩

namespace expandAndCancel

def formula : ℝ :=
  -2

theorem correct (x : ℝ) :
    (x + 1) * (x - 2) - (x - 1) * x = (formula) :=
  (Checked.expandAndCancel x).property

end expandAndCancel

def expandAndCancel {x : ℝ} :
    { y : ℝ // (x + 1) * (x - 2) - (x - 1) * x = y } :=
  ⟨expandAndCancel.formula, expandAndCancel.correct x⟩

namespace factorCubic

def formula (x : ℝ) : ℝ :=
  (x - 1) * (x ^ 2 + 1)

theorem correct (x : ℝ) :
    x ^ 3 - x ^ 2 + x - 1 = (formula x) :=
  (Checked.factorCubic x).property

end factorCubic

def factorCubic {x : ℝ} :
    { y : ℝ // x ^ 3 - x ^ 2 + x - 1 = y } :=
  ⟨factorCubic.formula x, factorCubic.correct x⟩

namespace factorMultivariate

def formula (x y z : ℝ) : ℝ :=
  z * (x + 2 * y) ^ 2

theorem correct (x y z : ℝ) :
    x ^ 2 * z + 4 * x * y * z + 4 * y ^ 2 * z = (formula x y z) :=
  (Checked.factorMultivariate x y z).property

end factorMultivariate

def factorMultivariate {x y z : ℝ} :
    { w : ℝ // x ^ 2 * z + 4 * x * y * z + 4 * y ^ 2 * z = w } :=
  ⟨factorMultivariate.formula x y z, factorMultivariate.correct x y z⟩

namespace collectPowers

def formula (x y z : ℝ) : ℝ :=
  x ^ 3 + (2 - z) * x ^ 2 + (y + 1) * x - 3

theorem correct (x y z : ℝ) :
    x * y + x - 3 + 2 * x ^ 2 - z * x ^ 2 + x ^ 3 = (formula x y z) :=
  (Checked.collectPowers x y z).property

end collectPowers

def collectPowers {x y z : ℝ} :
    { w : ℝ // x * y + x - 3 + 2 * x ^ 2 - z * x ^ 2 + x ^ 3 = w } :=
  ⟨collectPowers.formula x y z, collectPowers.correct x y z⟩

namespace quadraticCoefficient

def formula (z : ℝ) : ℝ :=
  2 - z

theorem correct (y z : ℝ) :
    (Polynomial.X ^ 3 + Polynomial.C (2 - z) * Polynomial.X ^ 2 +
        Polynomial.C (y + 1) * Polynomial.X - Polynomial.C 3).coeff 2 = (formula z) :=
  (Checked.quadraticCoefficient y z).property

end quadraticCoefficient

def quadraticCoefficient {y z : ℝ} :
    { c : ℝ //
      (Polynomial.X ^ 3 + Polynomial.C (2 - z) * Polynomial.X ^ 2 +
        Polynomial.C (y + 1) * Polynomial.X - Polynomial.C 3).coeff 2 = c } :=
  ⟨quadraticCoefficient.formula z, quadraticCoefficient.correct y z⟩

namespace cancelRational

def formula (x : ℝ) : ℝ :=
  (x + 1) / x

theorem correct (x : ℝ) (hx : x ≠ 0 := by assumption)
    (hx1 : x + 1 ≠ 0 := by assumption) :
    (x ^ 2 + 2 * x + 1) / (x ^ 2 + x) = (formula x) :=
  (Checked.cancelRational x hx hx1).property

end cancelRational

def cancelRational {x : ℝ} (hx : x ≠ 0 := by assumption) (hx1 : x + 1 ≠ 0 := by assumption) :
    { y : ℝ // (x ^ 2 + 2 * x + 1) / (x ^ 2 + x) = y } :=
  ⟨cancelRational.formula x, cancelRational.correct x hx hx1⟩

namespace partialFractions

def formula (x : ℝ) : ℝ :=
  (2 * x - 1) / (x ^ 2 + x + 1) - 1 / (x + 4) + 3 / x

theorem correct (x : ℝ) (hx : x ≠ 0 := by assumption)
    (hx4 : x + 4 ≠ 0 := by assumption) :
    (4 * x ^ 3 + 21 * x ^ 2 + 10 * x + 12) /
        (x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x) = (formula x) :=
  (Checked.partialFractions x hx hx4).property

end partialFractions

def partialFractions {x : ℝ} (hx : x ≠ 0 := by assumption) (hx4 : x + 4 ≠ 0 := by assumption) :
    { y : ℝ //
      (4 * x ^ 3 + 21 * x ^ 2 + 10 * x + 12) /
        (x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x) = y } :=
  ⟨partialFractions.formula x, partialFractions.correct x hx hx4⟩

namespace expandTrig

def formula (x y : ℝ) : ℝ :=
  Real.sin x * Real.cos y + Real.sin y * Real.cos x

theorem correct (x y : ℝ) :
    Real.sin (x + y) = (formula x y) :=
  (Checked.expandTrig x y).property

end expandTrig

def expandTrig {x y : ℝ} :
    { z : ℝ // Real.sin (x + y) = z } :=
  ⟨expandTrig.formula x y, expandTrig.correct x y⟩

namespace combineTrig

def formula (x y : ℝ) : ℝ :=
  Real.sin (x + y)

theorem correct (x y : ℝ) :
    Real.sin x * Real.cos y + Real.sin y * Real.cos x = (formula x y) :=
  (Checked.combineTrig x y).property

end combineTrig

def combineTrig {x y : ℝ} :
    { z : ℝ // Real.sin x * Real.cos y + Real.sin y * Real.cos x = z } :=
  ⟨combineTrig.formula x y, combineTrig.correct x y⟩

namespace simplifyHyperbolic

def formula (x : ℝ) : ℝ :=
  Real.cosh (2 * x)

theorem correct (x : ℝ) :
    Real.cosh x ^ 2 + Real.sinh x ^ 2 = (formula x) :=
  (Checked.simplifyHyperbolic x).property

end simplifyHyperbolic

def simplifyHyperbolic {x : ℝ} :
    { y : ℝ // Real.cosh x ^ 2 + Real.sinh x ^ 2 = y } :=
  ⟨simplifyHyperbolic.formula x, simplifyHyperbolic.correct x⟩

namespace combinePowers

def formula (x a b : ℝ) : ℝ :=
  x ^ (a + b)

theorem correct (x a b : ℝ) (hx : 0 < x := by assumption) :
    x ^ a * x ^ b = (formula x a b) :=
  (Checked.combinePowers x a b hx).property

end combinePowers

def combinePowers {x a b : ℝ} (hx : 0 < x := by assumption) :
    { y : ℝ // x ^ a * x ^ b = y } :=
  ⟨combinePowers.formula x a b, combinePowers.correct x a b hx⟩

namespace expandPowerBase

def formula (x y a : ℝ) : ℝ :=
  x ^ a * y ^ a

theorem correct (x y a : ℝ) (hx : 0 ≤ x := by assumption)
    (hy : 0 ≤ y := by assumption) :
    (x * y) ^ a = (formula x y a) :=
  (Checked.expandPowerBase x y a hx hy).property

end expandPowerBase

def expandPowerBase {x y a : ℝ} (hx : 0 ≤ x := by assumption) (hy : 0 ≤ y := by assumption) :
    { z : ℝ // (x * y) ^ a = z } :=
  ⟨expandPowerBase.formula x y a, expandPowerBase.correct x y a hx hy⟩

namespace denestPower

def formula (x a b : ℝ) : ℝ :=
  x ^ (a * b)

theorem correct (x a b : ℝ) (hx : 0 ≤ x := by assumption) :
    (x ^ a) ^ b = (formula x a b) :=
  (Checked.denestPower x a b hx).property

end denestPower

def denestPower {x a b : ℝ} (hx : 0 ≤ x := by assumption) :
    { y : ℝ // (x ^ a) ^ b = y } :=
  ⟨denestPower.formula x a b, denestPower.correct x a b hx⟩

namespace expandLog

def formula (x y : ℝ) : ℝ :=
  Real.log x + Real.log y

theorem correct (x y : ℝ) (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    Real.log (x * y) = (formula x y) :=
  (Checked.expandLog x y hx hy).property

end expandLog

def expandLog {x y : ℝ} (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    { z : ℝ // Real.log (x * y) = z } :=
  ⟨expandLog.formula x y, expandLog.correct x y hx hy⟩

namespace combineLog

def formula (x y : ℝ) : ℝ :=
  Real.log (x * y)

theorem correct (x y : ℝ) (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    Real.log x + Real.log y = (formula x y) :=
  (Checked.combineLog x y hx hy).property

end combineLog

def combineLog {x y : ℝ} (hx : 0 < x := by assumption) (hy : 0 < y := by assumption) :
    { z : ℝ // Real.log x + Real.log y = z } :=
  ⟨combineLog.formula x y, combineLog.correct x y hx hy⟩

namespace expandLogPower

def formula (x a : ℝ) : ℝ :=
  a * Real.log x

theorem correct (x a : ℝ) (hx : 0 < x := by assumption) :
    Real.log (x ^ a) = (formula x a) :=
  (Checked.expandLogPower x a hx).property

end expandLogPower

def expandLogPower {x a : ℝ} (hx : 0 < x := by assumption) :
    { y : ℝ // Real.log (x ^ a) = y } :=
  ⟨expandLogPower.formula x a, expandLogPower.correct x a hx⟩

namespace simplifySqrtSquare

def formula (x : ℝ) : ℝ :=
  |x|

theorem correct (x : ℝ) :
    Real.sqrt (x ^ 2) = (formula x) :=
  (Checked.simplifySqrtSquare x).property

end simplifySqrtSquare

def simplifySqrtSquare {x : ℝ} :
    { y : ℝ // Real.sqrt (x ^ 2) = y } :=
  ⟨simplifySqrtSquare.formula x, simplifySqrtSquare.correct x⟩

namespace rewriteFactorial

def formula (n : ℕ) : ℝ :=
  Real.Gamma (n + 1)

theorem correct (n : ℕ) :
    (n.factorial : ℝ) = (formula n) :=
  (Checked.rewriteFactorial n).property

end rewriteFactorial

def rewriteFactorial {n : ℕ} :
    { y : ℝ // (n.factorial : ℝ) = y } :=
  ⟨rewriteFactorial.formula n, rewriteFactorial.correct n⟩

namespace expandGamma

def formula (x : ℝ) : ℝ :=
  x * (x + 1) * (x + 2) * Real.Gamma x

theorem correct (x : ℝ) (hx : 0 < x := by assumption) :
    Real.Gamma (x + 3) = (formula x) :=
  (Checked.expandGamma x hx).property

end expandGamma

def expandGamma {x : ℝ} (hx : 0 < x := by assumption) :
    { y : ℝ // Real.Gamma (x + 3) = y } :=
  ⟨expandGamma.formula x, expandGamma.correct x hx⟩

namespace simplifyGammaRatio

def formula (x : ℝ) : ℝ :=
  (x - 2) * (x - 1)

theorem correct (x : ℝ) (hx : 2 < x := by assumption) :
    Real.Gamma x / Real.Gamma (x - 2) = (formula x) :=
  (Checked.simplifyGammaRatio x hx).property

end simplifyGammaRatio

def simplifyGammaRatio {x : ℝ} (hx : 2 < x := by assumption) :
    { y : ℝ // Real.Gamma x / Real.Gamma (x - 2) = y } :=
  ⟨simplifyGammaRatio.formula x, simplifyGammaRatio.correct x hx⟩

namespace simplifyGammaReflection

def formula (x : ℝ) : ℝ :=
  Real.pi / Real.sin (Real.pi * x)

theorem correct (x : ℝ) :
    Real.Gamma x * Real.Gamma (1 - x) = (formula x) :=
  (Checked.simplifyGammaReflection x).property

end simplifyGammaReflection

def simplifyGammaReflection {x : ℝ} :
    { y : ℝ // Real.Gamma x * Real.Gamma (1 - x) = y } :=
  ⟨simplifyGammaReflection.formula x, simplifyGammaReflection.correct x⟩

namespace simplifyFactorialRatio

def formula (n : ℕ) : ℚ :=
  (n + 3) * (n + 2) * (n + 1)

theorem correct (n : ℕ) :
    ((n + 3).factorial : ℚ) / n.factorial = (formula n) :=
  (Checked.simplifyFactorialRatio n).property

end simplifyFactorialRatio

def simplifyFactorialRatio {n : ℕ} :
    { y : ℚ // ((n + 3).factorial : ℚ) / n.factorial = y } :=
  ⟨simplifyFactorialRatio.formula n, simplifyFactorialRatio.correct n⟩

namespace continuedFraction

def formula : ℚ :=
  43 / 30

theorem correct :
    (1 + 1 / (2 + 1 / (3 + 1 / 4)) : ℚ) = (formula) :=
  (Checked.continuedFraction).property

end continuedFraction

def continuedFraction :
    { y : ℚ // (1 + 1 / (2 + 1 / (3 + 1 / 4)) : ℚ) = y } :=
  ⟨continuedFraction.formula, continuedFraction.correct⟩

namespace differentiateCos

def formula : ℝ → ℝ :=
  fun x ↦ -Real.sin x

theorem correct :
    ∀ x, HasDerivAt Real.cos ((formula) x) x :=
  (Checked.differentiateCos).property

end differentiateCos

def differentiateCos :
    { g : ℝ → ℝ // ∀ x, HasDerivAt Real.cos (g x) x } :=
  ⟨differentiateCos.formula, differentiateCos.correct⟩

namespace differentiateExpSquare

def formula : ℝ → ℝ :=
  fun x ↦ 2 * x * Real.exp (x ^ 2)

theorem correct :
    ∀ x, HasDerivAt (fun t ↦ Real.exp (t ^ 2)) ((formula) x) x :=
  (Checked.differentiateExpSquare).property

end differentiateExpSquare

def differentiateExpSquare :
    { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t ^ 2)) (g x) x } :=
  ⟨differentiateExpSquare.formula, differentiateExpSquare.correct⟩

namespace thirdDerivative

def formula : ℝ → ℝ :=
  fun x ↦ 24 * x

theorem correct :
    ∀ x, iteratedDeriv 3 (fun t : ℝ ↦ t ^ 4) x = (formula) x :=
  (Checked.thirdDerivative).property

end thirdDerivative

def thirdDerivative :
    { g : ℝ → ℝ // ∀ x, iteratedDeriv 3 (fun t : ℝ ↦ t ^ 4) x = g x } :=
  ⟨thirdDerivative.formula, thirdDerivative.correct⟩

namespace partialDerivative

def formula (y z : ℝ) : ℝ → ℝ :=
  fun x ↦ y * z * Real.exp (x * y * z)

theorem correct (y z : ℝ) :
    ∀ x, HasDerivAt (fun t ↦ Real.exp (t * y * z)) ((formula y z) x) x :=
  (Checked.partialDerivative y z).property

end partialDerivative

def partialDerivative {y z : ℝ} :
    { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t * y * z)) (g x) x } :=
  ⟨partialDerivative.formula y z, partialDerivative.correct y z⟩

namespace antiderivativeCos

def formula : ℝ → ℝ :=
  Real.sin

theorem correct :
    ∀ x, HasDerivAt (formula) (Real.cos x) x :=
  (Checked.antiderivativeCos).property

end antiderivativeCos

def antiderivativeCos :
    { F : ℝ → ℝ // ∀ x, HasDerivAt F (Real.cos x) x } :=
  ⟨antiderivativeCos.formula, antiderivativeCos.correct⟩

namespace antiderivativeLogSquare

def formula : ℝ → ℝ :=
  fun x ↦ x * Real.log x ^ 2 - 2 * x * Real.log x + 2 * x

theorem correct :
    ∀ x, 0 < x → HasDerivAt (formula) (Real.log x ^ 2) x :=
  (Checked.antiderivativeLogSquare).property

end antiderivativeLogSquare

def antiderivativeLogSquare :
    { F : ℝ → ℝ // ∀ x, 0 < x → HasDerivAt F (Real.log x ^ 2) x } :=
  ⟨antiderivativeLogSquare.formula, antiderivativeLogSquare.correct⟩

namespace integratePower

def formula : ℝ :=
  1 / 3

theorem correct :
    (∫ x : ℝ in 0..1, x ^ 2) = (formula) :=
  (Checked.integratePower).property

end integratePower

def integratePower :
    { y : ℝ // (∫ x : ℝ in 0..1, x ^ 2) = y } :=
  ⟨integratePower.formula, integratePower.correct⟩

namespace integrateCos

def formula (a b : ℝ) : ℝ :=
  Real.sin b - Real.sin a

theorem correct (a b : ℝ) :
    (∫ x : ℝ in a..b, Real.cos x) = (formula a b) :=
  (Checked.integrateCos a b).property

end integrateCos

def integrateCos {a b : ℝ} :
    { y : ℝ // (∫ x : ℝ in a..b, Real.cos x) = y } :=
  ⟨integrateCos.formula a b, integrateCos.correct a b⟩

namespace integrateExponentialTail

def formula : ℝ :=
  1

theorem correct :
    (∫ x : ℝ in Set.Ioi 0, Real.exp (-x)) = (formula) :=
  (Checked.integrateExponentialTail).property

end integrateExponentialTail

def integrateExponentialTail :
    { y : ℝ // (∫ x : ℝ in Set.Ioi 0, Real.exp (-x)) = y } :=
  ⟨integrateExponentialTail.formula, integrateExponentialTail.correct⟩

namespace integrateGaussian

def formula : ℝ :=
  Real.sqrt Real.pi

theorem correct :
    (∫ x : ℝ, Real.exp (-(x ^ 2))) = (formula) :=
  (Checked.integrateGaussian).property

end integrateGaussian

def integrateGaussian :
    { y : ℝ // (∫ x : ℝ, Real.exp (-(x ^ 2))) = y } :=
  ⟨integrateGaussian.formula, integrateGaussian.correct⟩

namespace numericIntegral

def formula : ℚ :=
  707 / 1000

theorem correct :
    |(∫ x : ℝ in 0..1, Real.sqrt 2 * x) - ((formula) : ℝ)| ≤ 1 / 1000 :=
  (Checked.numericIntegral).property

end numericIntegral

def numericIntegral :
    { q : ℚ // |(∫ x : ℝ in 0..1, Real.sqrt 2 * x) - (q : ℝ)| ≤ 1 / 1000 } :=
  ⟨numericIntegral.formula, numericIntegral.correct⟩

namespace limitSinc

def formula : ℝ :=
  1

theorem correct :
    Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 (formula)) :=
  (Checked.limitSinc).property

end limitSinc

def limitSinc :
    { y : ℝ // Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 y) } :=
  ⟨limitSinc.formula, limitSinc.correct⟩

namespace limitPolynomialOverExp

def formula : ℝ :=
  0

theorem correct :
    Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp x) atTop (𝓝 (formula)) :=
  (Checked.limitPolynomialOverExp).property

end limitPolynomialOverExp

def limitPolynomialOverExp :
    { y : ℝ // Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp x) atTop (𝓝 y) } :=
  ⟨limitPolynomialOverExp.formula, limitPolynomialOverExp.correct⟩

namespace expSeries

def formula : ℝ → ℝ :=
  fun x ↦ 1 + x + x ^ 2 / 2 + x ^ 3 / 6

theorem correct :
    (fun x ↦ Real.exp x - (formula) x) =O[𝓝 (0 : ℝ)] (fun x ↦ x ^ 4) :=
  (Checked.expSeries).property

end expSeries

def expSeries :
    { p : ℝ → ℝ // (fun x ↦ Real.exp x - p x) =O[𝓝 (0 : ℝ)] (fun x ↦ x ^ 4) } :=
  ⟨expSeries.formula, expSeries.correct⟩

namespace finiteDifference

def formula (x : ℝ) : ℝ :=
  2 * x

theorem correct (x h : ℝ) (hh : h ≠ 0 := by assumption) :
    ((x + h) ^ 2 - (x - h) ^ 2) / (2 * h) = (formula x) :=
  (Checked.finiteDifference x h hh).property

end finiteDifference

def finiteDifference {x h : ℝ} (hh : h ≠ 0 := by assumption) :
    { y : ℝ // ((x + h) ^ 2 - (x - h) ^ 2) / (2 * h) = y } :=
  ⟨finiteDifference.formula x, finiteDifference.correct x h hh⟩

namespace solveSquare

def formula : Set ℝ :=
  {-1, 1}

theorem correct :
    ∀ x, x ∈ (formula) ↔ x ^ 2 = 1 :=
  (Checked.solveSquare).property

end solveSquare

def solveSquare :
    { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 = 1 } :=
  ⟨solveSquare.formula, solveSquare.correct⟩

namespace solveQuadratic

def formula : Set ℝ :=
  {0, 1}

theorem correct :
    ∀ x, x ∈ (formula) ↔ x ^ 2 - x = 0 :=
  (Checked.solveQuadratic).property

end solveQuadratic

def solveQuadratic :
    { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 - x = 0 } :=
  ⟨solveQuadratic.formula, solveQuadratic.correct⟩

namespace solveIdentity

def formula : Set ℝ :=
  Set.univ

theorem correct :
    ∀ x, x ∈ (formula) ↔ x - x = 0 :=
  (Checked.solveIdentity).property

end solveIdentity

def solveIdentity :
    { S : Set ℝ // ∀ x, x ∈ S ↔ x - x = 0 } :=
  ⟨solveIdentity.formula, solveIdentity.correct⟩

namespace solveExponential

def formula : Set ℝ :=
  ∅

theorem correct :
    ∀ x, x ∈ (formula) ↔ Real.exp x = 0 :=
  (Checked.solveExponential).property

end solveExponential

def solveExponential :
    { S : Set ℝ // ∀ x, x ∈ S ↔ Real.exp x = 0 } :=
  ⟨solveExponential.formula, solveExponential.correct⟩

namespace solveLinearSystem

def formula : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 = -p.2.1 - 1 ∧ p.2.2 = 2}

theorem correct :
    ∀ x y z,
      (x, y, z) ∈ (formula) ↔ x + y + z = 1 ∧ x + y + 2 * z = 3 :=
  (Checked.solveLinearSystem).property

end solveLinearSystem

def solveLinearSystem :
    { S : Set (ℝ × ℝ × ℝ) // ∀ x y z,
      (x, y, z) ∈ S ↔ x + y + z = 1 ∧ x + y + 2 * z = 3 } :=
  ⟨solveLinearSystem.formula, solveLinearSystem.correct⟩

namespace solveNonlinearSystem

def formula : Set (ℝ × ℝ) :=
  {(2, 1 / 2)}

theorem correct :
    ∀ x y, (x, y) ∈ (formula) ↔ x * y = 1 ∧ x = 2 :=
  (Checked.solveNonlinearSystem).property

end solveNonlinearSystem

def solveNonlinearSystem :
    { S : Set (ℝ × ℝ) // ∀ x y, (x, y) ∈ S ↔ x * y = 1 ∧ x = 2 } :=
  ⟨solveNonlinearSystem.formula, solveNonlinearSystem.correct⟩

namespace solveODE

def formula (c₁ c₂ : ℝ) : ℝ → ℝ :=
  fun x ↦ (c₁ + c₂ * x) * Real.exp x + Real.cos x / 2

theorem correct (c₁ c₂ : ℝ) :
    ∀ x, deriv (deriv (formula c₁ c₂)) x - 2 * deriv (formula c₁ c₂) x +
      (formula c₁ c₂) x = Real.sin x :=
  (Checked.solveODE c₁ c₂).property

end solveODE

def solveODE (c₁ c₂ : ℝ) :
    { f : ℝ → ℝ // ∀ x, deriv (deriv f) x - 2 * deriv f x + f x = Real.sin x } :=
  ⟨solveODE.formula c₁ c₂, solveODE.correct c₁ c₂⟩

namespace matrixAdd

def formula : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, 6; -2, 10]

theorem correct :
    !![1, 3; -2, 3] + !![0, 3; 0, 7] = (formula) :=
  (Checked.matrixAdd).property

end matrixAdd

def matrixAdd :
    { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] + !![0, 3; 0, 7] = A } :=
  ⟨matrixAdd.formula, matrixAdd.correct⟩

namespace matrixMultiply

def formula : Matrix (Fin 2) (Fin 2) ℚ :=
  !![0, 24; 0, 15]

theorem correct :
    !![1, 3; -2, 3] * !![0, 3; 0, 7] = (formula) :=
  (Checked.matrixMultiply).property

end matrixMultiply

def matrixMultiply :
    { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] * !![0, 3; 0, 7] = A } :=
  ⟨matrixMultiply.formula, matrixMultiply.correct⟩

namespace matrixVectorProduct

def formula : Fin 2 → ℚ :=
  ![5, 3]

theorem correct :
    (!![1, 2, 3; 3, 2, 1] : Matrix (Fin 2) (Fin 3) ℚ) *ᵥ
      ![0, 1, 1] = (formula) :=
  (Checked.matrixVectorProduct).property

end matrixVectorProduct

def matrixVectorProduct :
    { v : Fin 2 → ℚ // (!![1, 2, 3; 3, 2, 1] : Matrix (Fin 2) (Fin 3) ℚ) *ᵥ
      ![0, 1, 1] = v } :=
  ⟨matrixVectorProduct.formula, matrixVectorProduct.correct⟩

namespace matrixTranspose

def formula : Matrix (Fin 3) (Fin 2) ℚ :=
  !![1, 4; 2, 5; 3, 6]

theorem correct :
    (!![1, 2, 3; 4, 5, 6] :
      Matrix (Fin 2) (Fin 3) ℚ).transpose = (formula) :=
  (Checked.matrixTranspose).property

end matrixTranspose

def matrixTranspose :
    { A : Matrix (Fin 3) (Fin 2) ℚ // (!![1, 2, 3; 4, 5, 6] :
      Matrix (Fin 2) (Fin 3) ℚ).transpose = A } :=
  ⟨matrixTranspose.formula, matrixTranspose.correct⟩

namespace matrixDeterminant

def formula : ℚ :=
  -1

theorem correct :
    (!![1, 0, 1; 2, -1, 3; 4, 3, 2] : Matrix (Fin 3) (Fin 3) ℚ).det = (formula) :=
  (Checked.matrixDeterminant).property

end matrixDeterminant

def matrixDeterminant :
    { d : ℚ // (!![1, 0, 1; 2, -1, 3; 4, 3, 2] : Matrix (Fin 3) (Fin 3) ℚ).det = d } :=
  ⟨matrixDeterminant.formula, matrixDeterminant.correct⟩

namespace matrixInverse

def formula : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 / 3, -1 / 3; 2 / 9, 1 / 9]

theorem correct :
    (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) * (formula) = 1 ∧
      (formula) * (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) = 1 :=
  (Checked.matrixInverse).property

end matrixInverse

def matrixInverse :
    { B : Matrix (Fin 2) (Fin 2) ℚ //
      (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) * B = 1 ∧
      B * (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) = 1 } :=
  ⟨matrixInverse.formula, matrixInverse.correct⟩

namespace matrixNullspace

def formula : ℚ → ℚ → ℚ → (Fin 5 → ℚ) :=
  fun a b c ↦ ![-15 * a + c, 6 * a - c / 2, a, b, c]

theorem correct :
    ∀ w : Fin 5 → ℚ,
      (!![1, 2, 3, 0, 0; 4, 10, 0, 0, 1] : Matrix (Fin 2) (Fin 5) ℚ) *ᵥ w = 0 ↔
        ∃ a b c, w = (formula) a b c :=
  (Checked.matrixNullspace).property

end matrixNullspace

def matrixNullspace :
    { v : ℚ → ℚ → ℚ → (Fin 5 → ℚ) // ∀ w : Fin 5 → ℚ,
      (!![1, 2, 3, 0, 0; 4, 10, 0, 0, 1] : Matrix (Fin 2) (Fin 5) ℚ) *ᵥ w = 0 ↔
        ∃ a b c, w = v a b c } :=
  ⟨matrixNullspace.formula, matrixNullspace.correct⟩

namespace matrixColumnspace

def formula : Fin 2 → Fin 3 → ℚ :=
  ![![1, 2, 3], ![1, 1, 1]]

theorem correct :
    (∀ w : Fin 3 → ℚ,
        (∃ v, (!![1, 1, 2; 2, 1, 3; 3, 1, 4] : Matrix (Fin 3) (Fin 3) ℚ) *ᵥ v = w) ↔
          ∃ a c : ℚ, w = a • (formula) 0 + c • (formula) 1) ∧
      Function.Injective (fun c : Fin 2 → ℚ ↦ c 0 • (formula) 0 + c 1 • (formula) 1) :=
  (Checked.matrixColumnspace).property

end matrixColumnspace

def matrixColumnspace :
    { b : Fin 2 → Fin 3 → ℚ //
      (∀ w : Fin 3 → ℚ,
        (∃ v, (!![1, 1, 2; 2, 1, 3; 3, 1, 4] : Matrix (Fin 3) (Fin 3) ℚ) *ᵥ v = w) ↔
          ∃ a c : ℚ, w = a • b 0 + c • b 1) ∧
      Function.Injective (fun c : Fin 2 → ℚ ↦ c 0 • b 0 + c 1 • b 1) } :=
  ⟨matrixColumnspace.formula, matrixColumnspace.correct⟩

namespace matrixCharacteristicPolynomial

def formula : Polynomial ℚ :=
  (Polynomial.X + 2) * (Polynomial.X - 3) * (Polynomial.X - 5) ^ 2

theorem correct :
    (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
        Matrix (Fin 4) (Fin 4) ℚ).charpoly = (formula) :=
  (Checked.matrixCharacteristicPolynomial).property

end matrixCharacteristicPolynomial

def matrixCharacteristicPolynomial :
    { p : Polynomial ℚ //
      (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
        Matrix (Fin 4) (Fin 4) ℚ).charpoly = p } :=
  ⟨matrixCharacteristicPolynomial.formula, matrixCharacteristicPolynomial.correct⟩

namespace rewriteSubexpression

def formula (x y : ℝ) : ℝ :=
  x * (x + y + 1)

theorem correct (x y : ℝ) :
    x ^ 2 + x * (y + 1) = (formula x y) :=
  (Checked.rewriteSubexpression x y).property

end rewriteSubexpression

def rewriteSubexpression {x y : ℝ} :
    { z : ℝ // x ^ 2 + x * (y + 1) = z } :=
  ⟨rewriteSubexpression.formula x y, rewriteSubexpression.correct x y⟩

namespace delayedExpression

def formula (x : ℝ) : ℝ :=
  x ^ 2 + 2 * x + 1

theorem correct (x : ℝ) :
    (fun t : ℝ ↦ (t + 1) ^ 2) x = (formula x) :=
  (Checked.delayedExpression x).property

end delayedExpression

def delayedExpression {x : ℝ} :
    { y : ℝ // (fun t : ℝ ↦ (t + 1) ^ 2) x = y } :=
  ⟨delayedExpression.formula x, delayedExpression.correct x⟩

theorem reciprocalRightLimit :
    Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop := Checked.reciprocalRightLimit

namespace matrixRref

def formula : Matrix (Fin 3) (Fin 4) ℚ :=
  !![1, 0, 1, 3; 0, 1, 2 / 3, 1 / 3; 0, 0, 0, 0]

theorem correct : Checked.matrixRref.operations *
    (!![1, 0, 1, 3; 2, 3, 4, 7; -1, -3, -3, -4] : Matrix (Fin 3) (Fin 4) ℚ) = formula :=
  Checked.matrixRref.correct

end matrixRref

abbrev RowReduction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) := Checked.RowReduction A

def matrixRref : RowReduction
    (!![1, 0, 1, 3; 2, 3, 4, 7; -1, -3, -3, -4] : Matrix (Fin 3) (Fin 4) ℚ) :=
  Checked.matrixRref

namespace matrixDiagonalization

def formula : Matrix (Fin 4) (Fin 4) ℚ × Matrix (Fin 4) (Fin 4) ℚ :=
  ( !![0, 1, 1, 0; 1, 1, 1, -1; 1, 1, 1, 0; 1, 1, 0, 1],
    Matrix.diagonal ![-2, 3, 5, 5] )

theorem correct :
    (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
      Matrix (Fin 4) (Fin 4) ℚ) =
      formula.1 * formula.2 * Checked.matrixDiagonalization.inverse := by
  change _ = Checked.matrixDiagonalization.basis *
    Matrix.diagonal Checked.matrixDiagonalization.eigenvalues *
      Checked.matrixDiagonalization.inverse
  rw [← Checked.matrixDiagonalization.eigenvectors, Matrix.mul_assoc,
    Checked.matrixDiagonalization.basis_mul_inverse, Matrix.mul_one]

end matrixDiagonalization

abbrev Diagonalization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) := Checked.Diagonalization A

def matrixDiagonalization : Diagonalization
    (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
      Matrix (Fin 4) (Fin 4) ℚ) := Checked.matrixDiagonalization

end

end SympyAI
