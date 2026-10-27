module

public import Z2Z4Rank6.SecondParameterCounting
public import Z2Z4Rank6.SecondFamilyCurveHeight
public import Z2Z4Rank6.BoundedHeightCounting
public import Z2Z4Rank6.SecondSingularFibers

@[expose] public section

/-!
# Second-family counts using primitive-short curve height

Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117. The primitive short
height has a proved comparison with the 12th power of reduced W-height.
The base has a proved function-field identification, rank 2 and
all-place correspondence, so its full bounded-parameter count has exponent 1.
The generic elementary height transport gives the same exponent for
normalized curve-height bounds; deleting singular points is finite.
-/

namespace Z2Z4Rank6.SecondCurveHeightCounting
open SecondFamily
noncomputable section

def curveHeight (P : G2Point ℚ) : ℕ := SecondFamilyCurveHeight.height P.W
def heightSet (H : ℕ) : Set (G2Point ℚ) := BoundedHeightCounting.boundedSet curveHeight H
def count (H : ℕ) : ℕ := BoundedHeightCounting.count curveHeight H
def goodParameters : Set (G2Point ℚ) := {P | GoodCurve (F P.W)}
def goodCount (H : ℕ) : ℕ := BoundedHeightCounting.restrictedCount curveHeight goodParameters H

theorem counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀ H,(heightSet H).Finite) ∧ HasLogarithmicCountingExponent count 1 := by
  obtain ⟨L,U,hL,hU,hBounds⟩ := SecondFamilyCurveHeight.height_bounds
  obtain ⟨hFinite,hCount⟩ := SecondParameterCounting.counting hN hMW hMazur hDescent
  exact BoundedHeightCounting.counting_of_power_comparison
    (h:=SecondParameterCounting.parameterHeight) (k:=curveHeight)
    (a:=1) (d:=12) hFinite hCount (by norm_num) hL hU (by decide)
    (fun P => hBounds P.W)

theorem goodParameters_compl_finite : goodParametersᶜ.Finite :=
  SecondCofiniteSpecialization.singularPoints_finite

theorem good_counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀ H,(heightSet H∩goodParameters).Finite) ∧
      HasLogarithmicCountingExponent goodCount 1 := by
  obtain ⟨hFinite,hCount⟩ := counting hN hMW hMazur hDescent
  exact BoundedHeightCounting.counting_on_cofinite_set hFinite hCount
    (by norm_num) goodParameters_compl_finite

end
end Z2Z4Rank6.SecondCurveHeightCounting
