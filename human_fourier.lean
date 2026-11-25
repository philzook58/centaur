module
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import ai_fourier
open FourierAI
open MeasureTheory
open FourierTransform
-- difference between open and open scoped ?
open Complex

open scoped Real


-- How do I access a fourier transform?
-- Delta functions?
--
noncomputable section

-- Should i make everyting complex?
-- I don't want to

/-
Should I used the 2 pi definition or just import mathlib's definition?
-/

def fourier_transform (f : Real -> Complex) (ω : Real) : Complex :=
  ∫ t : Real, (f t) * (exp (-I * ω * t))

#check (proof1_complex : fourier_transform (fun t => exp (- t ^ 2)) =
        fun (ω : Real) => √Real.pi * exp (-ω ^ 2 / 4))
#check (trans_gauss : {f : Real -> Complex // fourier_transform (fun t => exp (- t ^ 2))  = f})
#print trans_gauss.formula
--#check (f_exp : { f : Real -> Real //  Fourier (exp -t^2) } )

#check (𝓕 : (ℝ → ℂ) → (ℝ → ℂ))
/-

fourier is easier to spell of same thing
-/
#check 𝓕
#check fourier
-- Why isn't the notation found ? Hmm. super generic types ?
-- \ MCF to type that symbol

#check (trans_gauss2 : {f : Real -> Complex // 𝓕 (fun (t : Real) => cexp (- t ^ 2))  = f})
/-
Is there a clean way to avoid having t= real
-/

/-
Using a separate file is kind of not what lean vs code wants me to be doing
-/
-- Ctrl shift X to restart file


-- How much of the time is now ai time vs lean time?

-- Ok how fast is the response now?

-- How fast is it now?

abbrev FT := (𝓕 : (ℝ → ℂ) → (ℝ → ℂ))
-- Is there a predefined box function I should use?
-- I'm trying to think of things that even have fourier trasnforms
def box (t : Real) : Complex := if t <= 1 /\  t >= -1 then 1 else 0
def box2 : Real -> Complex := Set.Icc (-1 : Real) 1 |>.indicator (fun _ => 1)

example : box2 3 = 0 := by
  norm_num [box2]
example : box 3 = 0 := by
  norm_num [box]
