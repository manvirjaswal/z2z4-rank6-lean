module

public import Z2Z4Rank6.ProjectiveBaseSchemeGlobalSections
public import Z2Z4Rank6.ProjectiveBaseSchemeH1
public import Z2Z4Rank6.ProjectiveBaseSchemeDimension
public import Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
public import Z2Z4Rank6.ProjectiveBaseSchemePrintedPoint
public import Z2Z4Rank6.SmoothProperGeometricIntegrality

@[expose] public section

/-!
# Genus one of the projective base

Jaswal, Lemma 4.1(a), DOI 10.5281/zenodo.23437117. The scheme is the
Proj of the displayed homogeneous intersection. Its dimension,
properness, smoothness, global functions and rational point are proved.
Its structure-sheaf H1 has dimension one, by the published affine-cover comparison. These are
precisely the genus
conditions in Stacks Definition 53.8.1 (tag 0BY6).

The geometric-integrality variant also supplies the smooth-proper global-constants criterion.
-/

namespace Z2Z4Rank6.ProjectiveBaseSchemeGenus
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme StructureSheafCohomology

/-- The proper-curve genus-one conditions: dimension 1,
canonical H0=Q and finite-dimensional H1 of dimension 1. -/
theorem arithmetic_genus_one (hCohom : AffineCoverStructureSheafCohomologyTheorem) :
    IsProper structureMap ∧ SmoothOfRelativeDimension 1 structureMap ∧
      IsIntegral scheme ∧ topologicalKrullDim scheme=1 ∧
      Function.Bijective (qToGlobal scheme structureMap) ∧
      FiniteDimensional ℚ (H1 scheme structureMap) ∧
      Module.finrank ℚ (H1 scheme structureMap)=1 ∧
      Nonempty ProjectiveBaseSchemeRationalPoints.RationalPoint :=
  ⟨inferInstance,inferInstance,inferInstance,
    ProjectiveBaseScheme.scheme_topologicalKrullDim,
    ProjectiveBaseSchemeGlobalSections.global_constants_bijective,
    ProjectiveBaseSchemeH1.h1_finiteDimensional hCohom,
    ProjectiveBaseSchemeH1.h1_finrank hCohom,
    ⟨ProjectiveBaseSchemePrintedPoint.printedPoint⟩⟩

/-- The base remains integral after geometric field base change. -/
theorem geometrically_integral
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral structureMap :=
  SmoothProperGeometricIntegrality.geometricallyIntegral_of_global_constants
    hGeo scheme structureMap inferInstance ProjectiveBaseScheme.structureMap_smooth_morphism
    ProjectiveBaseSchemeGlobalSections.global_constants_bijective

/-- Lemma 4.1(a): the displayed projective intersection is a smooth,
geometrically integral proper curve of genus 1 with a rational point. -/
theorem lemma_4_1_a (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral structureMap ∧
      IsProper structureMap ∧ SmoothOfRelativeDimension 1 structureMap ∧
      IsIntegral scheme ∧ topologicalKrullDim scheme=1 ∧
      Function.Bijective (qToGlobal scheme structureMap) ∧
      FiniteDimensional ℚ (H1 scheme structureMap) ∧
      Module.finrank ℚ (H1 scheme structureMap)=1 ∧
      Nonempty ProjectiveBaseSchemeRationalPoints.RationalPoint :=
  ⟨geometrically_integral hGeo,arithmetic_genus_one hCohom⟩

/-- The projective scheme has infinitely many rational points,
using the already proved point equivalence and infinite-order argument. -/
theorem rationalPoints_infinite (hOdd : OddPrimeTorsionIntegrality) :
    Infinite ProjectiveBaseSchemeRationalPoints.RationalPoint := by
  let : Infinite CPoint := infinite_CPoint hOdd
  exact Infinite.of_injective ProjectiveBaseSchemeRationalPoints.rationalPointEquiv
    ProjectiveBaseSchemeRationalPoints.rationalPointEquiv.injective

end
end Z2Z4Rank6.ProjectiveBaseSchemeGenus
