import Z2Z4Rank6.ProjectiveBaseSchemeSections
import Z2Z4Rank6.StructureSheafGlobalSections
import Z2Z4Rank6.AffineBaseCechConstants
import Z2Z4Rank6.TwoChartKernelTransport
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Global functions of the projective base are rational constants

The structure-sheaf gluing isomorphism, the proved chart
restriction diagrams and the constant Laurent intersection give
H0=Q. The canonical coefficient ring homomorphism is proved bijective.
-/

namespace Z2Z4Rank6.ProjectiveBaseSchemeGlobalSections
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeSections
open StructureSheafCohomology AffineBaseFunctionFieldIso

abbrev leftRestriction := restriction scheme structureMap zOpen (zOpen⊓mOpen) inf_le_left
abbrev rightRestriction := restriction scheme structureMap mOpen (zOpen⊓mOpen) inf_le_right

/-- Compatible sheaf sections are exactly compatible
coordinate-ring pairs, in the proved Laurent coordinates. -/
def compatibleSectionsEquiv :
    StructureSheafGlobalSections.Compatible scheme structureMap zOpen mOpen≃ₗ[ℚ]
      LinearMap.ker AffineBaseCechConstants.restrictionDifference :=
  TwoChartKernelTransport.equiv leftRestriction rightRestriction
    AffineBaseCechRanges.positiveRestriction NegativeLaurentRange.negativeRestriction
    zSectionsEquiv mSectionsEquiv (overlapSectionsEquiv.trans overlapCoordinates)
    (fun a => congrArg overlapCoordinates (zRestriction_apply a))
    (fun a => congrArg overlapCoordinates (mRestriction_apply a))

/-- Global sections of the projective scheme form Q. -/
def globalSectionsEquiv : sectionModule scheme structureMap ⊤≃ₗ[ℚ]ℚ :=
  ((StructureSheafGlobalSections.globalEquivCompatible scheme structureMap zOpen mOpen
    two_chart_cover).trans compatibleSectionsEquiv).trans
      AffineBaseCechConstants.compatiblePairsEquiv

theorem global_sections_finrank : Module.finrank ℚ (sectionModule scheme structureMap ⊤)=1 := by
  simpa using globalSectionsEquiv.finrank_eq

/-- The canonical Q→Γ(Cbar,O) is bijective, not just an
unspecified rational vector-space isomorphism. -/
theorem global_constants_bijective : Function.Bijective (qToGlobal scheme structureMap) := by
  let : Algebra ℚ (GlobalRing scheme) := (qToGlobal scheme structureMap).toAlgebra
  let f : GlobalRing scheme→+ℚ := globalSectionsEquiv.toAddEquiv.toAddMonoidHom
  let e : GlobalRing scheme≃ₗ[ℚ]ℚ :=
    LinearEquiv.ofBijective f.toRatLinearMap globalSectionsEquiv.bijective
  change Function.Bijective (algebraMap ℚ (GlobalRing scheme))
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  simpa using e.finrank_eq

end
end Z2Z4Rank6.ProjectiveBaseSchemeGlobalSections
