import Z2Z4Rank6.TorsionCoverProjectiveGlobalSections
import Z2Z4Rank6.TorsionCoverProjectiveH1
import Z2Z4Rank6.TorsionCoverProjectiveSmooth
import Z2Z4Rank6.TorsionCoverDimension
import Z2Z4Rank6.TorsionCoverProjectiveRationalPoints
import Z2Z4Rank6.SmoothProperGeometricIntegrality

/-!
# Genus seventeen of both printed square-obstruction covers

Jaswal, Section 6, DOI 10.5281/zenodo.23437117. These are the
weighted Proj schemes r²=±A(z,m)B(z,m) over the displayed biquadratic base.
The two-chart calculation gives canonical H0=Q and
structure-sheaf H1 of dimension 17. Together with proved properness and
dimension 1 this is precisely genus 17 in Stacks Definition 53.8.1 (tag 0BY6).
The two published hypotheses are those used for the base curve.
-/
namespace Z2Z4Rank6.TorsionCoverGenus
noncomputable section
open AlgebraicGeometry CategoryTheory
open TorsionCoverProjective StructureSheafCohomology
variable (ε : Bool)

theorem arithmetic_genus_seventeen (hCohom : AffineCoverStructureSheafCohomologyTheorem) :
    IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) ∧
      topologicalKrullDim (scheme ε)=1 ∧
      Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) ∧
      FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) ∧
      Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=17 ∧
      Nonempty (TorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨inferInstance,inferInstance,TorsionCoverDimension.scheme_topologicalKrullDim ε,
    TorsionCoverProjectiveGlobalSections.global_constants_bijective ε,
    TorsionCoverProjectiveH1.h1_finiteDimensional ε hCohom,
    TorsionCoverProjectiveH1.h1_finrank ε hCohom,
    ⟨TorsionCoverProjectiveRationalPoints.branchPoint ε⟩⟩

theorem geometrically_integral
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap ε) :=
  SmoothProperGeometricIntegrality.geometricallyIntegral_of_global_constants
    hGeo (scheme ε) (structureMap ε) inferInstance (structureMap_smooth_morphism ε)
    (TorsionCoverProjectiveGlobalSections.global_constants_bijective ε)

/-- Both signed projective square-obstruction covers are smooth,
geometrically integral curves of genus 17, with rational branch points. -/
theorem genus_seventeen (hCohom : AffineCoverStructureSheafCohomologyTheorem)
    (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    GeometricallyIntegral (structureMap ε) ∧
      IsProper (structureMap ε) ∧ SmoothOfRelativeDimension 1 (structureMap ε) ∧
      topologicalKrullDim (scheme ε)=1 ∧
      Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) ∧
      FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) ∧
      Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=17 ∧
      Nonempty (TorsionCoverProjectiveRationalPoints.RationalPoint ε) :=
  ⟨geometrically_integral ε hGeo,arithmetic_genus_seventeen ε hCohom⟩

end
end Z2Z4Rank6.TorsionCoverGenus
