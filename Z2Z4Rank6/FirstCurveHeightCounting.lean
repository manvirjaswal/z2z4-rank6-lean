module

public import Z2Z4Rank6.CParameterCounting
public import Z2Z4Rank6.FamilyCurveHeight
public import Z2Z4Rank6.BoundedHeightCounting

@[expose] public section

/-!
# First-family counts using the normalized elliptic-curve height

Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117. The height is computed
from a primitive integral short Weierstrass representative, with an
admissible change from the rational fiber. Its comparison with the
48th power of reduced parameter height is proved. The generic Néron input
therefore gives logarithmic exponent 1/2 for the bounded C-point sets.
Deleting the proved finite singular set preserves the count exponent.
-/

namespace Z2Z4Rank6.FirstCurveHeightCounting
noncomputable section

def curveHeight (c : CPoint) : ℕ := FamilyCurveHeight.height c.m
def heightSet (H : ℕ) : Set CPoint := BoundedHeightCounting.boundedSet curveHeight H
def count (H : ℕ) : ℕ := BoundedHeightCounting.count curveHeight H
def goodParameters : Set CPoint := {c | GoodCurve (X c.m)}
def goodCount (H : ℕ) : ℕ := BoundedHeightCounting.restrictedCount curveHeight goodParameters H

/-- Bounded sets are finite, and the normalized curve-height
count has exponent 1/2. -/
theorem counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) :
    (∀ H,(heightSet H).Finite) ∧ HasLogarithmicCountingExponent count (1/2) := by
  obtain ⟨L,U,hL,hU,hBounds⟩ := FamilyCurveHeight.height_bounds
  apply BoundedHeightCounting.counting_of_power_comparison
    (h:=fun c : CPoint => rationalParameterHeight c.m) (k:=curveHeight)
    (a:=1/2) (d:=48) ?_ ?_ (by norm_num) hL hU (by decide)
    (fun c => hBounds c.m)
  · exact CParameterCounting.heightSet_finite hN hMW hDescent hOdd
  · exact CParameterCounting.counting_exponent hN hMW hDescent hOdd

theorem goodParameters_compl_finite : goodParametersᶜ.Finite := by
  have he : goodParametersᶜ=exceptionalPoints := by
    ext c
    simp only [goodParameters,Set.mem_compl_iff,Set.mem_ofPred_eq,X_good_iff_not_exceptional,
      not_not]
  rw [he]
  exact exceptionalPoints_finite

/-- Smooth first-family fibers retain the normalized curve-height
exponent after removing precisely the singular rational points. -/
theorem good_counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) :
    (∀ H,(heightSet H∩goodParameters).Finite) ∧
      HasLogarithmicCountingExponent goodCount (1/2) := by
  obtain ⟨hFinite,hCount⟩ := counting hN hMW hDescent hOdd
  exact BoundedHeightCounting.counting_on_cofinite_set hFinite hCount
    (by norm_num) goodParameters_compl_finite

end
end Z2Z4Rank6.FirstCurveHeightCounting
