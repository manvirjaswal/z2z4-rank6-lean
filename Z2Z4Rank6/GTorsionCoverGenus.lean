module

public import Z2Z4Rank6.GTorsionCoverProjectiveGlobalSections
public import Z2Z4Rank6.GTorsionCoverProjectiveH1
public import Z2Z4Rank6.GTorsionCoverProjectiveSmooth
public import Z2Z4Rank6.GTorsionCoverDimension
public import Z2Z4Rank6.GTorsionCoverProjectiveRationalPoints
public import Z2Z4Rank6.SmoothProperGeometricIntegrality

@[expose] public section

/-!
# Genus nine of both printed square-obstruction covers

Jaswal, Section 7, DOI 10.5281/zenodo.23437117. These are the
weighted Proj schemes r²=±a(m)b(m) over the quartic G.
The two-chart calculation gives canonical H0=Q and
structure-sheaf H1 of dimension 9. Together with proved properness and
dimension 1 this is precisely genus 9 in Stacks Definition 53.8.1 (tag 0BY6).
The two published hypotheses are those used for the base curve.
-/
namespace Z2Z4Rank6.GTorsionCoverGenus
noncomputable section
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective StructureSheafCohomology
variable (ε : Bool)

theorem arithmetic_genus_nine (hCohom : AffineCoverStructureSheafCohomologyTheorem) :
    IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) ∧
      topologicalKrullDim (scheme ε)=1 ∧
      Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) ∧
      FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) ∧
      Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=9 ∧
      Nonempty (GTorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨inferInstance,inferInstance,GTorsionCoverDimension.scheme_topologicalKrullDim ε,
    GTorsionCoverProjectiveGlobalSections.global_constants_bijective ε,
    GTorsionCoverProjectiveH1.h1_finiteDimensional ε hCohom,
    GTorsionCoverProjectiveH1.h1_finrank ε hCohom,
    ⟨GTorsionCoverProjectiveRationalPoints.branchPoint ε⟩⟩

theorem geometrically_integral
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap ε) :=
  SmoothProperGeometricIntegrality.geometricallyIntegral_of_global_constants
    hGeo (scheme ε) (structureMap ε) inferInstance (structureMap_smooth_morphism ε)
    (GTorsionCoverProjectiveGlobalSections.global_constants_bijective ε)

/-- Both signed projective square-obstruction covers are smooth,
geometrically integral curves of genus 9, with rational branch points. -/
theorem genus_nine (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap ε) ∧
      IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) ∧
      topologicalKrullDim (scheme ε)=1 ∧
      Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) ∧
      FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) ∧
      Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=9 ∧
      Nonempty (GTorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨geometrically_integral ε hGeo,arithmetic_genus_nine ε hCohom⟩

end
end Z2Z4Rank6.GTorsionCoverGenus
