module

public import Z2Z4Rank6.SecondTorsionCoverProjectiveGlobalSections
public import Z2Z4Rank6.SecondTorsionCoverProjectiveH1
public import Z2Z4Rank6.SecondTorsionCoverProjectiveSmooth
public import Z2Z4Rank6.SecondTorsionCoverDimension
public import Z2Z4Rank6.SecondTorsionCoverProjectiveRationalPoints
public import Z2Z4Rank6.SmoothProperGeometricIntegrality

@[expose] public section

/-!
# Genus nine of both printed square-obstruction covers

Jaswal, Section 8, DOI 10.5281/zenodo.23437117. These are the
weighted Proj schemes r²=±V(W) over the displayed second base, with W=(M/Z)².
The two-chart calculation gives canonical H0=Q and
structure-sheaf H1 of dimension 9. Together with proved properness and
dimension 1 this is precisely genus 9 in Stacks Definition 53.8.1 (tag 0BY6).
The two published hypotheses are those used for the base curve.
-/
namespace Z2Z4Rank6.SecondTorsionCoverGenus
noncomputable section
open AlgebraicGeometry CategoryTheory
open SecondTorsionCoverProjective StructureSheafCohomology
variable (ε : Bool)

theorem arithmetic_genus_nine (hCohom : AffineCoverStructureSheafCohomologyTheorem) :
    IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) ∧
      topologicalKrullDim (scheme ε)=1 ∧
      Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) ∧
      FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) ∧
      Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=9 ∧
      Nonempty (SecondTorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨inferInstance,inferInstance,SecondTorsionCoverDimension.scheme_topologicalKrullDim ε,
    SecondTorsionCoverProjectiveGlobalSections.global_constants_bijective ε,
    SecondTorsionCoverProjectiveH1.h1_finiteDimensional ε hCohom,
    SecondTorsionCoverProjectiveH1.h1_finrank ε hCohom,
    ⟨SecondTorsionCoverProjectiveRationalPoints.branchPoint ε⟩⟩

theorem geometrically_integral
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap ε) :=
  SmoothProperGeometricIntegrality.geometricallyIntegral_of_global_constants
    hGeo (scheme ε) (structureMap ε) inferInstance (structureMap_smooth_morphism ε)
    (SecondTorsionCoverProjectiveGlobalSections.global_constants_bijective ε)

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
      Nonempty (SecondTorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨geometrically_integral ε hGeo,arithmetic_genus_nine ε hCohom⟩

end
end Z2Z4Rank6.SecondTorsionCoverGenus
