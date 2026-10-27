module

public import Z2Z4Rank6.FirstCurveHeightCounting
public import Z2Z4Rank6.FiniteImageCounting

@[expose] public section

/-!
# Distinct first-family j-values of bounded curve height

The primitive short curve height, parameter count and 192-point
j-fiber bound give exponent 1/2. Source: Jaswal, Remark 6.3,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.FirstHeightRemark
open FirstCurveHeightCounting
noncomputable section

def jImageSet (S : Set CPoint) (H : ℕ) : Set ℚ :=
  (fun c : CPoint => jValue (X c.m)) '' (heightSet H∩S)

def jCount (S : Set CPoint) (H : ℕ) : ℕ := (jImageSet S H).ncard

theorem counting_on_cofinite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (S : Set CPoint)
    (hExceptional : Sᶜ.Finite) (hSmooth : ∀ c∈S,GoodCurve (X c.m)) :
    (∀ H,(jImageSet S H).Finite) ∧ HasLogarithmicCountingExponent (jCount S) (1/2) := by
  obtain ⟨hFinite,hCount⟩ := FirstCurveHeightCounting.counting hN hMW hDescent hOdd
  obtain ⟨hRestricted,hRestrictedCount⟩ := BoundedHeightCounting.counting_on_cofinite_set
    hFinite hCount (by norm_num) hExceptional
  refine ⟨fun H => (hRestricted H).image _,?_⟩
  apply hRestrictedCount.of_eventually_mul_sandwich (C:=192) (by norm_num) (by decide)
  apply Filter.Eventually.of_forall
  intro H
  exact ⟨Set.ncard_image_le (hRestricted H),
    ncard_CPoint_le_192_mul_jimage _ (hRestricted H) (fun c hc => hSmooth c hc.2)⟩

/-- The first-family assertion of Remark 6.3, with an infinite sequence of
finite j-value sets counted by the primitive-short curve height. -/
theorem remark_6_3_first_family (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) :
    (∀ H,(jImageSet goodParameters H).Finite) ∧
      HasLogarithmicCountingExponent (jCount goodParameters) (1/2) :=
  counting_on_cofinite hN hMW hDescent hOdd goodParameters
    goodParameters_compl_finite (fun _ hc => hc)

end
end Z2Z4Rank6.FirstHeightRemark
