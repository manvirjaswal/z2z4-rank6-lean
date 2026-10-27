module

public import Z2Z4Rank6.FirstBaseGeometry

@[expose] public section

/-!
# All assertions of Lemma 4.1(b)

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(b). The displayed
isomorphism is an isomorphism of the complete curves over Q. Rank,
torsion and infinite order concern the Mathlib rational point group.
The canonical affine-chart equivalence identifies all rational points of
the complete first base with the printed affine points. The conductor uses
the minimal-regular-proper-model component definition.
-/

namespace Z2Z4Rank6.FirstBaseJacobianArithmetic
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.Elliptic.GeometricConductor Common.Elliptic.MulhollandModelTheorems

theorem lemma_4_1_b
    (hIso : SmoothProperCurveFunctionFieldIsomorphismTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (hMazur : MazurTorsionTheorem)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOddComponents : Theorems23And24SemistableComponents) :
    Nonempty {e : ProjectiveBaseScheme.scheme ≅ ECProjectiveScheme.scheme //
      e.hom ≫ ECProjectiveScheme.structureMap = ProjectiveBaseScheme.structureMap} ∧
    PrintedModelConductorData.conductor hModels 0 = 9240 ∧
    TorsionExact EC ∧
    AddSubgroup.closure ({ecTwoGenerator,ecFourGenerator} : Set (RationalPoints EC)) =
      AddCommGroup.torsion (RationalPoints EC) ∧
    Module.rank ℤ (RationalPoints EC) = 1 ∧
    ¬ IsOfFinAddOrder ecP ∧
    Infinite ProjectiveBaseSchemeRationalPoints.RationalPoint ∧
    Function.Bijective ProjectiveBaseSchemeRationalPoints.fromAffine := by
  exact ⟨BaseProjectiveSchemeIsomorphism.theorem_1_2_a_isomorphism hIso,
    PrintedModelConductors.ec_conductor hModels h21 hOddComponents,
    ec_torsion_exact hMazur,ec_printed_generators hMazur,
    ec_rank_eq_one hMW hDescent hOdd,ecP_infinite_order hOdd,
    ProjectiveBaseSchemeGenus.rationalPoints_infinite hOdd,
    ProjectiveBaseSchemeRationalPoints.rationalPointEquiv.bijective⟩

end
end Z2Z4Rank6.FirstBaseJacobianArithmetic
