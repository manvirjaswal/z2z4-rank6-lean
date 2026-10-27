import Z2Z4Rank6.SecondFunctionFieldPointPlaceModel
import Z2Z4Rank6.SilvermanRigidSpecialization
import Z2Z4Rank6.SecondFunctionFieldSpecialization
import Z2Z4Rank6.SecondJTranscendence
import Z2Z4Rank6.CofiniteRankAssembly
import Z2Z4Rank6.SecondSingularFibers
import Mathlib.Algebra.Module.Rat

/-!
# Cofinite rank on the second rational parameter curve

The constructed normalized places carry the six independent generic points
to fibers outside a finite set. Source: Jaswal, Theorem 8.1(c),
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.SecondCofiniteSpecialization
open SecondFamily SecondFunctionFieldPointPlace
open CanonicalLaurentSpecialization
open scoped Classical
noncomputable section

local instance secondFamilyScalarTower :
    @IsScalarTower ℚ (RatFunc ℚ) SecondFunctionField.K
      (inferInstance : SMul ℚ (RatFunc ℚ))
      (Algebra.toSMul : SMul (RatFunc ℚ) SecondFunctionField.K)
      (Algebra.toSMul : SMul ℚ SecondFunctionField.K) := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=RatFunc ℚ) (A:=SecondFunctionField.K)
    (Subsingleton.elim _ _)

abbrev GoodParameters := {P : SecondFunctionFieldPointPlace.Point // GoodCurve (F P.val.W)}

local instance secondFamilyFiniteDimensional : FiniteDimensional (RatFunc ℚ) SecondFunctionField.K :=
  Module.Finite.of_basis SecondFunctionField.basis

def actualPlace (P : GoodParameters) :
    RigidGoodPlace SecondFunctionField.K (F SecondFunctionField.W) where
  parameter := P.val.val.W
  embedding := embeddingAlgHom P.val
  rigid := embeddingAlgHom_parameter P.val
  model := seriesCurve P.val
  model_eq := seriesCurve_laurent P.val
  good := constantFiber_elliptic P.val P.property

theorem actualPlace_injective : Function.Injective actualPlace := by
  intro P Q h
  apply Subtype.ext
  apply embeddingAlgHom_injective_on_points
  exact congrArg RigidGoodPlace.embedding h

theorem rankAtLeastSix_of_place_specialization
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (P : GoodParameters)
    (hP : RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace P)) :
    RankAtLeastSix (F P.val.val.W) := by
  obtain ⟨σ,hσ,_⟩ := hP
  let τ : (F SecondFunctionField.W).toAffine.Point →+ (F P.val.val.W).toAffine.Point :=
    (pointEquivOfEq (seriesCurve_constant P.val)).toAddMonoidHom.comp σ
  apply rankAtLeastSix_of_injective_hom SecondFunctionField.points
    (SecondFunctionField.points_independent hMazur hReduction hFormal) (F P.val.val.W) τ
  exact (pointEquivOfEq (seriesCurve_constant P.val)).injective.comp hσ

theorem finite_rank_failures
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    {P : G2Point ℚ | ¬RankAtLeastSix (F P.W)}.Finite := by
  have hbad := finite_bad_rigid_places hSilverman (F SecondFunctionField.W)
    inferInstance SecondFunctionField.j_transcendental
  have hpull : (actualPlace ⁻¹' RigidGoodPlace.badPlaces (F SecondFunctionField.W)).Finite :=
    hbad.preimage actualPlace_injective.injOn
  apply ((branchPoints_finite.union singularPoints_finite).union
    (hpull.image (fun P : GoodParameters => P.val.val))).subset
  intro P hP
  by_cases hb : P∈branchPoints
  · exact Or.inl (Or.inl hb)
  by_cases hg : GoodCurve (F P.W)
  · let p : SecondFunctionFieldPointPlace.Point := ⟨P,by
      change ¬(P.W=0 ∨ P.W=(beta:ℚ) ∨ P.W=(gamma:ℚ)) at hb
      tauto⟩
    let q : GoodParameters := ⟨p,hg⟩
    refine Or.inr ⟨q,?_,rfl⟩
    change ¬RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace q)
    intro hspec
    exact hP (rankAtLeastSix_of_place_specialization hMazur hReduction hFormal q hspec)
  · exact Or.inl (Or.inr hg)

end
end Z2Z4Rank6.SecondCofiniteSpecialization
