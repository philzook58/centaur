module

public import sympyai
public meta import sympyai

/-!
# A human-owned tour of symbolic mathematics

Companion to https://docs.sympy.org/latest/tutorials/intro-tutorial/index.html

Each typed `#check` is a request: a name, an input, and the property the answer must satisfy.
Declare variables once, describe the preferred form in a comment, and save. The companion agent
maintains the named terms in `sympyai.lean`; there are no human-side wrapper definitions.

Inspect `answer.formula` with `#print` and its certificate with `#check answer.correct`.
Use `answer.formula x` and `answer.correct x` in subsequent mathematics. The bundled answer
still provides `.val` and `.property`. Implicit parameters are inferred from each request's type;
assumptions live in short sections so unrelated requests do not inherit them.

This is a Lean adaptation covering the tutorial's mathematical operation families, rather than
a translation of every Python call. Real domains and side conditions are explicit. Python
installation, string parsing, printer backends, mutable matrices, and NumPy code generation
are programming interfaces; Lean uses imports, typed syntax, pretty printing, immutable matrices,
and executable definitions instead. Special-function examples here use Gamma and factorials;
the tutorial's general hypergeometric and Meijer-G transformations are not implemented here.

After these files have been created, a companion agent should edit only `sympyai.lean`.
The files demonstrate the request/answer convention; they do not start a watcher.

Check the complete pair with `lake build sympyhuman`.
-/

public section

section

open SympyAI Real Filter MeasureTheory
open scoped Topology Matrix

variable (x y z a b h c₁ c₂ : ℝ) (n : ℕ)

/-! ## Introduction, symbols, equality, and basic operations

Lean variables are typed symbols. `=` is mathematical equality; its proof is checked.
Use `^` for powers, and annotate fractions with `ℚ` or `ℝ` to avoid natural-number division.

Tutorial: introduction.html, gotchas.html, basic_operations.html
-/

-- Simplify sqrt(8), without specifying the desired answer.
#check (simplifyRadical : { y : ℝ // Real.sqrt 8 = y })
#print simplifyRadical.formula

-- I guess this makes no sense.
-- Substitute y for x in cos(x) + 1.
#check (substituteCos : { z : ℝ // (fun x ↦ Real.cos x + 1) y = z })
#print substituteCos

-- Substitute a numerical argument and simplify.
#check (substituteAtZero : { y : ℝ // Real.cos 0 + 1 = y })

-- Exact rational arithmetic, in contrast to a decimal approximation.
#check (exactRational : { y : ℚ // (1 / 3 : ℚ) + 1 / 6 = y })

-- evalf-style request with a mathematical accuracy requirement.
#check (sqrtTwoApprox : { q : ℚ // |Real.sqrt 2 - (q : ℝ)| ≤ 1 / 1000 })

-- lambdify-style use: the returned formula can itself be used as a function.
#check (substitutePower : { y : ℝ // x ^ 3 + 4 * x ^ 2 + 6 * x + 10 = y })

/-! ## Printing and inspecting answers

Tutorial: printing.html

`#check` shows types; `#print` shows definitions; `#eval` executes computable data.
Avoid fully reducing real-number constructions just to inspect a symbolic formula.
The `.formula` declarations print just the chosen data, without certificates.
-/

#check simplifyRadical.correct
#print simplifyRadical.formula
#print expandSquare.formula

-- Rational formulas can be evaluated directly.
#eval exactRational.formula
#eval continuedFraction.formula

/-! ## Simplification: polynomials and rational functions

Tutorial: simplification.html

The request comments describe the preferred form. Equality certifies correctness, not optimality
or irreducibility. Unlike generic rational-function cancellation, pointwise real identities must
account for removed poles: the assumptions below are part of the requests.
-/

#check (simplifyTrig : { y : ℝ // Real.sin x ^ 2 + Real.cos x ^ 2 = y })

section
variable (hx : x + 1 ≠ 0)

#check (simplifyRational : { y : ℝ // (x ^ 3 + x ^ 2 - x - 1) / (x ^ 2 + 2 * x + 1) = y })

end

-- Expand.
#check (expandSquare : { y : ℝ // (x + 1) ^ 2 = y })

#check (expandProduct : { y : ℝ // (x + 2) * (x - 3) = y })

#check (expandAndCancel : { y : ℝ // (x + 1) * (x - 2) - (x - 1) * x = y })

-- Factor.
#check (factorCubic : { y : ℝ // x ^ 3 - x ^ 2 + x - 1 = y })

#check (factorMultivariate : { w : ℝ // x ^ 2 * z + 4 * x * y * z + 4 * y ^ 2 * z = w })

-- Collect by powers of x, then extract the quadratic coefficient as polynomial data.
#check (collectPowers : { w : ℝ // x * y + x - 3 + 2 * x ^ 2 - z * x ^ 2 + x ^ 3 = w })

#check (quadraticCoefficient : { c : ℝ //
      (Polynomial.X ^ 3 + Polynomial.C (2 - z) * Polynomial.X ^ 2 +
        Polynomial.C (y + 1) * Polynomial.X - Polynomial.C 3).coeff 2 = c })

-- Cancel common factors. The imported term obtains hx and hx1 from this context.
section
variable (hx : x ≠ 0) (hx1 : x + 1 ≠ 0)

#check (cancelRational : { y : ℝ // (x ^ 2 + 2 * x + 1) / (x ^ 2 + x) = y })

end

-- Partial fractions.
section
variable (hx : x ≠ 0) (hx4 : x + 4 ≠ 0)

#check (partialFractions : { y : ℝ // (4 * x ^ 3 + 21 * x ^ 2 + 10 * x + 12) /
      (x ^ 4 + 5 * x ^ 3 + 5 * x ^ 2 + 4 * x) = y })

end

/-! ## Trigonometry, powers, and logarithms -/

#check (expandTrig : { z : ℝ // Real.sin (x + y) = z })

#check (combineTrig : { z : ℝ // Real.sin x * Real.cos y + Real.sin y * Real.cos x = z })

#check (simplifyHyperbolic : { y : ℝ // Real.cosh x ^ 2 + Real.sinh x ^ 2 = y })

section
variable (hx : 0 < x)

#check (combinePowers : { y : ℝ // x ^ a * x ^ b = y })

end

section
variable (hx : 0 ≤ x) (hy : 0 ≤ y)

#check (expandPowerBase : { z : ℝ // (x * y) ^ a = z })

end

section
variable (hx : 0 ≤ x)

#check (denestPower : { y : ℝ // (x ^ a) ^ b = y })

end

section
variable (hx : 0 < x) (hy : 0 < y)

#check (expandLog : { z : ℝ // Real.log (x * y) = z })

end

section
variable (hx : 0 < x) (hy : 0 < y)

#check (combineLog : { z : ℝ // Real.log x + Real.log y = z })

end

section
variable (hx : 0 < x)

#check (expandLogPower : { y : ℝ // Real.log (x ^ a) = y })

end

-- With no sign assumption the correct answer is an absolute value, not simply x.
#check (simplifySqrtSquare : { y : ℝ // Real.sqrt (x ^ 2) = y })

/-! ## Special functions, combinatorics, and continued fractions -/

-- Rewrite factorial using Gamma.
#check (rewriteFactorial : { y : ℝ // (n.factorial : ℝ) = y })

section
variable (hx : 0 < x)

#check (expandGamma : { y : ℝ // Real.Gamma (x + 3) = y })

end

section
variable (hx : 2 < x)

#check (simplifyGammaRatio : { y : ℝ // Real.Gamma x / Real.Gamma (x - 2) = y })

end

#check (simplifyGammaReflection : { y : ℝ // Real.Gamma x * Real.Gamma (1 - x) = y })

-- combsimp: use n+3 rather than n with an implicit n ≥ 3 requirement.
#check (simplifyFactorialRatio : { y : ℚ // ((n + 3).factorial : ℚ) / n.factorial = y })

-- The continued-fraction example adapted to the finite list [1; 2, 3, 4].
#check (continuedFraction : { y : ℚ // (1 + 1 / (2 + 1 / (3 + 1 / 4)) : ℚ) = y })

/-! ## Calculus

Tutorial: calculus.html

Differentiation returns a function with a derivative certificate. Antiderivatives specify their
domain. Limits use filters, including punctured and one-sided neighborhoods. Series return an
asymptotic remainder assertion. A finite difference is not asserted equal to a general derivative.
-/

#check (differentiateCos : { g : ℝ → ℝ // ∀ x, HasDerivAt Real.cos (g x) x })

#check (differentiateExpSquare :
    { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t ^ 2)) (g x) x })

#check (thirdDerivative : { g : ℝ → ℝ // ∀ x, iteratedDeriv 3 (fun t : ℝ ↦ t ^ 4) x = g x })

-- Differentiate exp(x*y*z) in x, keeping y and z as parameters.
#check (partialDerivative : { g : ℝ → ℝ // ∀ x, HasDerivAt (fun t ↦ Real.exp (t * y * z)) (g x) x })

#check (antiderivativeCos : { F : ℝ → ℝ // ∀ x, HasDerivAt F (Real.cos x) x })

#check (antiderivativeLogSquare : { F : ℝ → ℝ // ∀ x, 0 < x → HasDerivAt F (Real.log x ^ 2) x })

#check (integratePower : { y : ℝ // (∫ x : ℝ in 0..1, x ^ 2) = y })

#check (integrateCos : { y : ℝ // (∫ x : ℝ in a..b, Real.cos x) = y })

#check (integrateExponentialTail : { y : ℝ // (∫ x : ℝ in Set.Ioi 0, Real.exp (-x)) = y })

#check (integrateGaussian : { y : ℝ // (∫ x : ℝ, Real.exp (-(x ^ 2))) = y })

-- Numerical integration returns a rational approximation with a proved error bound.
#check (numericIntegral : { q : ℚ // |(∫ x : ℝ in 0..1, Real.sqrt 2 * x) - (q : ℝ)| ≤ 1 / 1000 })

#check (limitSinc : { y : ℝ // Tendsto (fun x : ℝ ↦ Real.sin x / x) (𝓝[≠] 0) (𝓝 y) })

#check (limitPolynomialOverExp : { y : ℝ // Tendsto (fun x : ℝ ↦ x ^ 2 / Real.exp x) atTop (𝓝 y) })

-- Infinite limits have a filter as target rather than a real-valued answer.
#check (reciprocalRightLimit : Tendsto (fun x : ℝ ↦ 1 / x) (𝓝[>] 0) atTop)

-- Adapt the series example to exp(x) through cubic order, with O(x^4) remainder.
#check (expSeries : { p : ℝ → ℝ // (fun x ↦ Real.exp x - p x) =O[𝓝 (0 : ℝ)] (fun x ↦ x ^ 4) })

-- A concrete finite-difference example: centered differences of a quadratic.
section
variable (hh : h ≠ 0)

#check (finiteDifference : { y : ℝ // ((x + h) ^ 2 - (x - h) ^ 2) / (2 * h) = y })

end

/-! ## Solvers

Tutorial: solvers.html

An equivalence gives ALL solutions over the specified domain. In contrast, the ODE request below
asks only for a solution family; its certificate does not claim that every solution is in it.
-/

#check (solveSquare : { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 = 1 })

#check (solveQuadratic : { S : Set ℝ // ∀ x, x ∈ S ↔ x ^ 2 - x = 0 })

#check (solveIdentity : { S : Set ℝ // ∀ x, x ∈ S ↔ x - x = 0 })

#check (solveExponential : { S : Set ℝ // ∀ x, x ∈ S ↔ Real.exp x = 0 })

#check (solveLinearSystem : { S : Set (ℝ × ℝ × ℝ) // ∀ x y z,
      (x, y, z) ∈ S ↔ x + y + z = 1 ∧ x + y + 2 * z = 3 })

#check (solveNonlinearSystem : { S : Set (ℝ × ℝ) // ∀ x y, (x, y) ∈ S ↔ x * y = 1 ∧ x = 2 })

#check (solveODE c₁ c₂ : { f : ℝ → ℝ // ∀ x, deriv (deriv f) x - 2 * deriv f x + f x = Real.sin x })

/-! ## Matrices

Tutorial: matrices.html

Dimensions are in the types. Entries are rational; returned matrices can be evaluated exactly.
An inverse request asks for both inverse identities. A nullspace request includes completeness
of the parametrization rather than merely checking several kernel vectors.
-/

#check (matrixAdd : { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] + !![0, 3; 0, 7] = A })

#check (matrixMultiply : { A : Matrix (Fin 2) (Fin 2) ℚ // !![1, 3; -2, 3] * !![0, 3; 0, 7] = A })

#check (matrixVectorProduct :
    { v : Fin 2 → ℚ // (!![1, 2, 3; 3, 2, 1] : Matrix (Fin 2) (Fin 3) ℚ) *ᵥ
      ![0, 1, 1] = v })

#check (matrixTranspose : { A : Matrix (Fin 3) (Fin 2) ℚ // (!![1, 2, 3; 4, 5, 6] :
      Matrix (Fin 2) (Fin 3) ℚ).transpose = A })

#check (matrixDeterminant :
    { d : ℚ // (!![1, 0, 1; 2, -1, 3; 4, 3, 2] : Matrix (Fin 3) (Fin 3) ℚ).det = d })

#check (matrixInverse : { B : Matrix (Fin 2) (Fin 2) ℚ //
      (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) * B = 1 ∧
      B * (!![1, 3; -2, 3] : Matrix (Fin 2) (Fin 2) ℚ) = 1 })

#check (matrixNullspace : { v : ℚ → ℚ → ℚ → (Fin 5 → ℚ) // ∀ w : Fin 5 → ℚ,
      (!![1, 2, 3, 0, 0; 4, 10, 0, 0, 1] : Matrix (Fin 2) (Fin 5) ℚ) *ᵥ w = 0 ↔
        ∃ a b c, w = v a b c })

-- Return a column basis: spanning the image, with unique coefficients.
#check (matrixColumnspace : { b : Fin 2 → Fin 3 → ℚ //
      (∀ w : Fin 3 → ℚ,
        (∃ v, (!![1, 1, 2; 2, 1, 3; 3, 1, 4] : Matrix (Fin 3) (Fin 3) ℚ) *ᵥ v = w) ↔
          ∃ a c : ℚ, w = a • b 0 + c • b 1) ∧
      Function.Injective (fun c : Fin 2 → ℚ ↦ c 0 • b 0 + c 1 • b 1) })

-- RREF includes an invertible matrix of row operations and a reduced-form proof.
#check (matrixRref : RowReduction
    (!![1, 0, 1, 3; 2, 3, 4, 7; -1, -3, -3, -4] : Matrix (Fin 3) (Fin 4) ℚ))

-- Eigenvectors form an invertible basis, with the corresponding eigenvalues returned as data.
#check (matrixDiagonalization : Diagonalization
    (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
      Matrix (Fin 4) (Fin 4) ℚ))

-- The factored characteristic polynomial records algebraic multiplicities.
#check (matrixCharacteristicPolynomial : { p : Polynomial ℚ //
      (!![3, -2, 4, -2; 5, 3, -3, -2; 5, -2, 2, -2; 5, -2, -3, 3] :
        Matrix (Fin 4) (Fin 4) ℚ).charpoly = p })

/-! ## Advanced expression manipulation

Tutorial: manipulation.html

Lean retains expressions such as `x + x` until a proof or computation rewrites them. A named
function provides delayed substitution, and a certified equality justifies a transformation.
For raw expression-tree inspection, `set_option pp.all true in #check ...` exposes elaborated
Lean syntax; its application tree differs from SymPy's Add/Mul/Pow representation.
-/

#check (rewriteSubexpression : { z : ℝ // x ^ 2 + x * (y + 1) = z })

#check (delayedExpression : { y : ℝ // (fun t : ℝ ↦ (t + 1) ^ 2) x = y })

-- Reuse the returned certificate directly in a subsequent high-level argument.
example : (x + 1) ^ 2 = expandSquare.formula x := expandSquare.correct x

-- Inspect just the returned real formula, series, or solution set.
#print factorCubic.formula
#print expSeries.formula
#print solveSquare.formula

-- Matrix answers: evaluate an individual entry (functions themselves have no useful #eval output).
#eval matrixMultiply.formula 0 1

end
