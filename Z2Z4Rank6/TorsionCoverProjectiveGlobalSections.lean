import Z2Z4Rank6.TorsionCoverProjectiveSections
import Z2Z4Rank6.StructureSheafGlobalSections
import Z2Z4Rank6.TorsionCoverCechAlgebra
import Z2Z4Rank6.TwoChartKernelTransport
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! Canonical global functions of the signed projective covers are Q.
The proof glues structure-sheaf sections, uses the proved
restriction diagrams, and computes the Laurent intersection.
-/
namespace Z2Z4Rank6.TorsionCoverProjectiveGlobalSections
noncomputable section
open AlgebraicGeometry CategoryTheory
open TorsionCoverProjective TorsionCoverProjectiveSections
open StructureSheafCohomology TorsionCoverOverlap
variable (ε : Bool)

abbrev leftRestriction := restriction (scheme ε) (structureMap ε) (zOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_left
abbrev rightRestriction := restriction (scheme ε) (structureMap ε) (mOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_right

def compatibleSectionsEquiv :
    StructureSheafGlobalSections.Compatible (scheme ε) (structureMap ε) (zOpen ε) (mOpen ε)≃ₗ[ℚ]
      LinearMap.ker (TorsionCoverCechAlgebra.differential ε) :=
  TwoChartKernelTransport.equiv (leftRestriction ε) (rightRestriction ε)
    (TorsionCoverCechRanges.positiveRestriction ε) (TorsionCoverCechRanges.negativeRestriction ε)
    (zSectionsEquiv ε) (mSectionsEquiv ε) ((overlapSectionsEquiv ε).trans (overlapCoordinates ε))
    (fun a => congrArg (overlapCoordinates ε) (zRestriction_apply ε a))
    (fun a => congrArg (overlapCoordinates ε) (mRestriction_apply ε a))

def globalSectionsEquiv : sectionModule (scheme ε) (structureMap ε) ⊤≃ₗ[ℚ]ℚ :=
  ((StructureSheafGlobalSections.globalEquivCompatible (scheme ε) (structureMap ε) (zOpen ε) (mOpen ε)
    (two_chart_cover ε)).trans (compatibleSectionsEquiv ε)).trans
      (TorsionCoverCechAlgebra.compatiblePairsEquiv ε)

theorem global_sections_finrank :
    Module.finrank ℚ (sectionModule (scheme ε) (structureMap ε) ⊤)=1 := by
  simpa using (globalSectionsEquiv ε).finrank_eq

theorem global_constants_bijective : Function.Bijective (qToGlobal (scheme ε) (structureMap ε)) := by
  let : Algebra ℚ (GlobalRing (scheme ε)) := (qToGlobal (scheme ε) (structureMap ε)).toAlgebra
  let f : GlobalRing (scheme ε)→+ℚ := (globalSectionsEquiv ε).toAddEquiv.toAddMonoidHom
  let e : GlobalRing (scheme ε)≃ₗ[ℚ]ℚ :=
    LinearEquiv.ofBijective f.toRatLinearMap (globalSectionsEquiv ε).bijective
  change Function.Bijective (algebraMap ℚ (GlobalRing (scheme ε)))
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  simpa using e.finrank_eq

end
end Z2Z4Rank6.TorsionCoverProjectiveGlobalSections
