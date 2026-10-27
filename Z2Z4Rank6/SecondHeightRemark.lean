module

public import Z2Z4Rank6.SecondCurveHeightCounting
public import Z2Z4Rank6.FiniteImageCounting

@[expose] public section

/-!
# Distinct second-family j-values of bounded curve height

The primitive short curve height and the 96-point j-fiber bound
transfer exponent 1 from rational base points to j-values.
Source: Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.SecondHeightRemark
open SecondFamily SecondCurveHeightCounting
noncomputable section

def jImageSet (S : Set (G2Point ℚ)) (H : ℕ) : Set ℚ :=
  (fun P : G2Point ℚ => jValue (F P.W)) '' (heightSet H∩S)
def jCount (S : Set (G2Point ℚ)) (H : ℕ) : ℕ := (jImageSet S H).ncard

theorem counting_on_cofinite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (S : Set (G2Point ℚ))
    (hExceptional : Sᶜ.Finite) (hSmooth : ∀ P∈S,GoodCurve (F P.W)) :
    (∀ H,(jImageSet S H).Finite) ∧ HasLogarithmicCountingExponent (jCount S) 1 := by
  obtain ⟨hFinite,hCount⟩ := SecondCurveHeightCounting.counting hN hMW hMazur hDescent
  obtain ⟨hRestricted,hRestrictedCount⟩ := BoundedHeightCounting.counting_on_cofinite_set
    hFinite hCount (by norm_num) hExceptional
  refine ⟨fun H => (hRestricted H).image _,?_⟩
  apply hRestrictedCount.of_eventually_mul_sandwich (C:=96) (by norm_num) (by decide)
  apply Filter.Eventually.of_forall
  intro H
  exact ⟨Set.ncard_image_le (hRestricted H),
    ncard_G2Point_le_96_mul_jimage _ (hRestricted H) (fun P hP => hSmooth P hP.2)⟩

/-- The second-family assertion of Remark 6.3 in terms of finite
j-image sets and the paper's primitive-short curve height. -/
theorem remark_6_3_second_family (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀ H,(jImageSet goodParameters H).Finite) ∧
      HasLogarithmicCountingExponent (jCount goodParameters) 1 :=
  counting_on_cofinite hN hMW hMazur hDescent goodParameters
    goodParameters_compl_finite (fun _ hP => hP)

end
end Z2Z4Rank6.SecondHeightRemark
