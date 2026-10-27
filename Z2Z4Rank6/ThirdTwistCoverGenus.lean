module

public import Z2Z4Rank6.ThirdTwistCoverProjectiveGlobalSections
public import Z2Z4Rank6.ThirdTwistCoverProjectiveH1
public import Z2Z4Rank6.ThirdTwistCoverProjectiveSmooth
public import Z2Z4Rank6.ThirdTwistCoverDimension
public import Z2Z4Rank6.ThirdTwistCoverProjectiveRationalPoints
public import Z2Z4Rank6.SmoothProperGeometricIntegrality

@[expose] public section

/-!
# Genus five of the third-twist base

The Proj of the three quadratic radical equations is smooth,
proper, geometrically integral and dimension 1. The chart calculation
proves canonical H0=Q and structure-sheaf H1 of dimension 5.
The hypotheses are the same cohomology and geometric integrality theorems as for the other
projective bases.
-/

namespace Z2Z4Rank6.ThirdTwistCoverGenus
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective StructureSheafCohomology

theorem arithmetic_genus_five (hCohom : AffineCoverStructureSheafCohomologyTheorem) :
    IsProper (structureMap) ∧ SmoothOfRelativeDimension 1 (structureMap) ∧
      topologicalKrullDim (scheme)=1 ∧
      Function.Bijective (qToGlobal (scheme) (structureMap)) ∧
      FiniteDimensional ℚ (H1 (scheme) (structureMap)) ∧
      Module.finrank ℚ (H1 (scheme) (structureMap))=5 ∧
      Nonempty (ThirdTwistCoverProjectiveRationalPoints.RationalPoint) :=
  ⟨inferInstance,inferInstance,ThirdTwistCoverDimension.scheme_topologicalKrullDim,
    ThirdTwistCoverProjectiveGlobalSections.global_constants_bijective,
    ThirdTwistCoverProjectiveH1.h1_finiteDimensional hCohom,
    ThirdTwistCoverProjectiveH1.h1_finrank hCohom,
    ⟨ThirdTwistCoverProjectiveRationalPoints.branchPoint⟩⟩

theorem geometrically_integral
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap) :=
  SmoothProperGeometricIntegrality.geometricallyIntegral_of_global_constants
    hGeo (scheme) (structureMap) inferInstance (structureMap_smooth_morphism)
    (ThirdTwistCoverProjectiveGlobalSections.global_constants_bijective)

/-- The third-twist projective base is smooth,
geometrically integral curves of genus 5, with a rational point. -/
theorem genus_five (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap) ∧
      IsProper (structureMap) ∧ SmoothOfRelativeDimension 1 (structureMap) ∧
      topologicalKrullDim (scheme)=1 ∧
      Function.Bijective (qToGlobal (scheme) (structureMap)) ∧
      FiniteDimensional ℚ (H1 (scheme) (structureMap)) ∧
      Module.finrank ℚ (H1 (scheme) (structureMap))=5 ∧
      Nonempty (ThirdTwistCoverProjectiveRationalPoints.RationalPoint) :=
  ⟨geometrically_integral hGeo,arithmetic_genus_five hCohom⟩

end
end Z2Z4Rank6.ThirdTwistCoverGenus
