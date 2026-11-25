module
import aijackson
/-
Bobby wondered if ai can do jackson.
Can it?
Probably
Can it help me formalize it?
Griffiths EM?

-/

noncomputable section

variable (φ ρ : Real ^ 3 -> Real)

def poisson φ ρ := ∇ φ = ρ
def laplace φ := ∇ φ = 0
