module

public import Z2Z4Rank6.FunctionFieldPointPlace
public import Z2Z4Rank6.SilvermanRigidSpecialization
public import Z2Z4Rank6.FunctionFieldSpecialization
public import Z2Z4Rank6.CofiniteRankAssembly
public import Z2Z4Rank6.SingularFibers
public import Z2Z4Rank6.JTranscendence
public import Mathlib.Algebra.Module.Rat

@[expose] public section

/-!
# Cofinite rank on the first rational parameter curve

The normalized rational places and generic independent points give
finitely many rank failures by the explicit generic specialization theorem.
Source: Jaswal, Theorem 1.2(c), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6
namespace CofiniteSpecialization

open FunctionFieldPointPlace
open CanonicalLaurentSpecialization
open scoped Classical
noncomputable section

/-- The Q-algebra structures passed to the generic finite-extension theorem
are compatible by uniqueness of rational ring homomorphisms. -/
local instance firstFamilyScalarTower :
    @IsScalarTower ℚ (RatFunc ℚ) FunctionField.K
      (inferInstance : SMul ℚ (RatFunc ℚ))
      (Algebra.toSMul : SMul (RatFunc ℚ) FunctionField.K)
      (Algebra.toSMul : SMul ℚ FunctionField.K) := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=RatFunc ℚ) (A:=FunctionField.K)
    (Subsingleton.elim _ _)

abbrev GoodParameters := {c : CPoint // c∉exceptionalPoints}

/-- The normalized good place at a rational C-point. -/
def actualPlace (c : GoodParameters) : RigidGoodPlace FunctionField.K (X FunctionField.m) where
  parameter := c.val.m
  embedding := embeddingAlgHom c.val
  rigid := embeddingAlgHom_parameter c.val
  model := seriesCurve c.val
  model_eq := seriesCurve_laurent c.val
  good := constantFiber_elliptic c.val c.property

/-- Recovering the three constant coordinates excludes duplicate places. -/
theorem actualPlace_injective : Function.Injective actualPlace := by
  intro c d h
  apply Subtype.ext
  apply embeddingAlgHom_injective_on_points
  exact congrArg RigidGoodPlace.embedding h

/-- Injectivity at this place yields six independent rational points
on this fiber. The underlying specialization is fully canonical. -/
theorem rankAtLeastSix_of_place_specialization
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (c : GoodParameters)
    (hc : RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace c)) :
    RankAtLeastSix (X c.val.m) := by
  obtain ⟨σ,hσ,_⟩ := hc
  let τ : (X FunctionField.m).toAffine.Point →+ (X c.val.m).toAffine.Point :=
    (pointEquivOfEq (seriesCurve_constant c.val)).toAddMonoidHom.comp σ
  apply rankAtLeastSix_of_injective_hom FunctionField.points
    (FunctionField.points_independent hMazur hReduction hFormal) (X c.val.m) τ
  exact (pointEquivOfEq (seriesCurve_constant c.val)).injective.comp hσ

/-- The finite set of bad normalized places pulls back to a finite set of
rational parameters, including the already proved sixteen singular ones. -/
theorem finite_rank_failures_of_transcendental
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hj : Transcendental ℚ (X FunctionField.m).j) :
    {c : CPoint | ¬RankAtLeastSix (X c.m)}.Finite := by
  let : FiniteDimensional FunctionField.Base FunctionField.K :=
    Module.Finite.of_basis FunctionField.basis
  have hbad := finite_bad_rigid_places hSilverman (X FunctionField.m) inferInstance hj
  have hpull : (actualPlace ⁻¹' RigidGoodPlace.badPlaces (X FunctionField.m)).Finite :=
    hbad.preimage actualPlace_injective.injOn
  apply (exceptionalPoints_finite.union (hpull.image Subtype.val)).subset
  intro c hc
  by_cases he : c∈exceptionalPoints
  · exact Or.inl he
  · refine Or.inr ⟨⟨c,he⟩,?_,rfl⟩
    change ¬RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace ⟨c,he⟩)
    intro hspec
    exact hc (rankAtLeastSix_of_place_specialization hMazur hReduction hFormal ⟨c,he⟩ hspec)

/-- The first-family fibers have rank at least six away from a finite
set. Nonconstant j and the required degree-four function-field data are proved. -/
theorem finite_rank_failures
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    {c : CPoint | ¬RankAtLeastSix (X c.m)}.Finite :=
  finite_rank_failures_of_transcendental hSilverman hMazur hReduction hFormal
    FunctionField.j_transcendental

/-- The cofinite rank assertion on the rational curve C. -/
theorem rankAtLeastSix_cofinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    ∀ᶠ c : CPoint in Filter.cofinite, RankAtLeastSix (X c.m) :=
  Filter.eventually_cofinite.mpr (finite_rank_failures hSilverman hMazur hReduction hFormal)

end
end CofiniteSpecialization
end Z2Z4Rank6
