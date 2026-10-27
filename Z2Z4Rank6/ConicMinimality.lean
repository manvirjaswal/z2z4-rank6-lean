module

public import Z2Z4Rank6.ConicRankNineModels
public import Z2Z4Rank6.Minimality
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

/-!
# Minimality of the conic rank-nine example

The printed equation in Proposition 7.1(b) of Jaswal,
DOI 10.5281/zenodo.23437117, is minimal at every rational prime. This uses
Mathlib's `WeierstrassCurve.IsMinimal` predicate over the p-adic
integers, proved from an integer Bezout identity for c₄ and discriminant.
The rank calculation is separate from the minimality argument below.
-/

namespace Z2Z4Rank6.ConicRankNine

noncomputable section

def integralPublishedModel : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -1443705842368492991301675445569878391286260
  a₆ := 518524534126954116322153225511662398609137586525877978241619600

theorem publishedModel_integral :
    integralPublishedModel.map (Int.castRingHom ℚ)=publishedModel := by
  ext <;> norm_num [integralPublishedModel,publishedModel]

/-- Kernel-checked Bezout certificate; c₄ and discriminant are coprime. -/
theorem integralPublishedModel_coprime :
    IsCoprime integralPublishedModel.c₄ integralPublishedModel.Δ := by
  refine ⟨36894041675017428731158443487677160210967009625918389628610106093368996335308377563035913462156562670484684049801261953241657921,
    -33450659594828496850812603905290989269926064,?_⟩
  norm_num [integralPublishedModel,WeierstrassCurve.c₄,WeierstrassCurve.Δ,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

/-- Local minimality at every rational prime. -/
theorem publishedModel_minimal (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsMinimal (PadicInt p)
      (publishedModel.map (Rat.castHom (Padic p))) := by
  let W : WeierstrassCurve (PadicInt p) :=
    integralPublishedModel.map (Int.castRingHom (PadicInt p))
  have hcop : IsCoprime W.c₄ W.Δ := by
    simpa only [W,WeierstrassCurve.map_c₄,WeierstrassCurve.map_Δ] using
      integralPublishedModel_coprime.map (Int.castRingHom (PadicInt p))
  have h := Minimality.baseChange_isMinimal_of_isCoprime (K:=Padic p) (PadicInt p) W hcop
  convert h using 1
  ext <;> norm_num [W,integralPublishedModel,publishedModel,WeierstrassCurve.baseChange,
    PadicInt.coe_natCast,PadicInt.coe_intCast]
  all_goals norm_cast

/-- Global minimality means local minimality at every rational prime. -/
def PublishedModelGlobalMinimal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], WeierstrassCurve.IsMinimal (PadicInt p)
    (publishedModel.map (Rat.castHom (Padic p)))

theorem publishedModel_global_minimal : PublishedModelGlobalMinimal := publishedModel_minimal

end
end Z2Z4Rank6.ConicRankNine
