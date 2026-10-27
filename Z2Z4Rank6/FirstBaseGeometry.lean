module

public import Z2Z4Rank6.ProjectiveBaseSchemeGenus
public import Z2Z4Rank6.BaseProjectiveSchemeIsomorphism
public import Z2Z4Rank6.ECExactRank
public import Z2Z4Rank6.BaseTorsion
public import Z2Z4Rank6.PrintedModelConductors

@[expose] public section

/-!
# Complete geometric and arithmetic base assertion in Theorem 1.2(a)

Jaswal, Theorem 1.2(a), DOI 10.5281/zenodo.23437117. The projective
base has genus one, infinitely many rational scheme points,
an over-Q isomorphism to the full printed EC cubic, conductor 9240
under the geometric definition, and Mathlib point-group
rank one. All its rational scheme points are exactly the printed affine
C points, via the canonical affine-chart equivalence.

The genus calculation uses
two-chart sheaf cohomology in place of the printed pencil argument.
-/

namespace Z2Z4Rank6.FirstBaseGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.Elliptic.GeometricConductor Common.Elliptic.MulhollandModelTheorems

theorem theorem_1_2_a
    (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (hIso : SmoothProperCurveFunctionFieldIsomorphismTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOddComponents : Theorems23And24SemistableComponents) :
    GeometricallyIntegral ProjectiveBaseScheme.structureMap ∧
      IsProper ProjectiveBaseScheme.structureMap ∧
      SmoothOfRelativeDimension 1 ProjectiveBaseScheme.structureMap ∧
      topologicalKrullDim ProjectiveBaseScheme.scheme = 1 ∧
      Function.Bijective (StructureSheafCohomology.qToGlobal
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) ∧
      FiniteDimensional ℚ (StructureSheafCohomology.H1
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) ∧
      Module.finrank ℚ (StructureSheafCohomology.H1
        ProjectiveBaseScheme.scheme ProjectiveBaseScheme.structureMap) = 1 ∧
      Infinite ProjectiveBaseSchemeRationalPoints.RationalPoint ∧
      Nonempty {e : ProjectiveBaseScheme.scheme ≅ ECProjectiveScheme.scheme //
        e.hom ≫ ECProjectiveScheme.structureMap = ProjectiveBaseScheme.structureMap} ∧
      PrintedModelConductorData.conductor hModels 0 = 9240 ∧
      Module.rank ℤ (RationalPoints EC) = 1 ∧
      Function.Bijective ProjectiveBaseSchemeRationalPoints.fromAffine := by
  exact ⟨ProjectiveBaseSchemeGenus.geometrically_integral hGeo,
    inferInstance,inferInstance,ProjectiveBaseScheme.scheme_topologicalKrullDim,
    ProjectiveBaseSchemeGlobalSections.global_constants_bijective,
    ProjectiveBaseSchemeH1.h1_finiteDimensional hCohom,
    ProjectiveBaseSchemeH1.h1_finrank hCohom,
    ProjectiveBaseSchemeGenus.rationalPoints_infinite hOdd,
    BaseProjectiveSchemeIsomorphism.theorem_1_2_a_isomorphism hIso,
    PrintedModelConductors.ec_conductor hModels h21 hOddComponents,
    ec_rank_eq_one hMW hDescent hOdd,
    ProjectiveBaseSchemeRationalPoints.rationalPointEquiv.bijective⟩

end
end Z2Z4Rank6.FirstBaseGeometry
