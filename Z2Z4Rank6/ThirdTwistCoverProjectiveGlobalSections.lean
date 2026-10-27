module

public import Z2Z4Rank6.ThirdTwistCoverProjectiveSections
public import Z2Z4Rank6.StructureSheafGlobalSections
public import Z2Z4Rank6.ThirdTwistCoverCechAlgebra
public import Z2Z4Rank6.TwoChartKernelTransport
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

@[expose] public section

/-! Canonical global functions of the third-twist projective base are Q.
The proof glues structure-sheaf sections, uses the proved
restriction diagrams, and computes the Laurent intersection.
-/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveGlobalSections
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveSections
open StructureSheafCohomology ThirdTwistCoverOverlap

abbrev leftRestriction := restriction (scheme) (structureMap) (zOpen) ((zOpen)⊓(mOpen)) inf_le_left
abbrev rightRestriction := restriction (scheme) (structureMap) (mOpen) ((zOpen)⊓(mOpen)) inf_le_right

def compatibleSectionsEquiv :
    StructureSheafGlobalSections.Compatible (scheme) (structureMap) (zOpen) (mOpen)≃ₗ[ℚ]
      LinearMap.ker (ThirdTwistCoverCechAlgebra.differential) :=
  TwoChartKernelTransport.equiv (leftRestriction) (rightRestriction)
    (ThirdTwistCoverCechRanges.positiveRestriction) (ThirdTwistCoverCechRanges.negativeRestriction)
    (zSectionsEquiv) (mSectionsEquiv) ((overlapSectionsEquiv).trans (overlapCoordinates))
    (fun a => congrArg (overlapCoordinates) (zRestriction_apply a))
    (fun a => congrArg (overlapCoordinates) (mRestriction_apply a))

def globalSectionsEquiv : sectionModule (scheme) (structureMap) ⊤≃ₗ[ℚ]ℚ :=
  ((StructureSheafGlobalSections.globalEquivCompatible (scheme) (structureMap) (zOpen) (mOpen)
    (two_chart_cover)).trans (compatibleSectionsEquiv)).trans
      (ThirdTwistCoverCechAlgebra.compatiblePairsEquiv)

theorem global_sections_finrank :
    Module.finrank ℚ (sectionModule (scheme) (structureMap) ⊤)=1 := by
  simpa using (globalSectionsEquiv).finrank_eq

theorem global_constants_bijective : Function.Bijective (qToGlobal (scheme) (structureMap)) := by
  let : Algebra ℚ (GlobalRing (scheme)) := (qToGlobal (scheme) (structureMap)).toAlgebra
  let f : GlobalRing (scheme)→+ℚ := (globalSectionsEquiv).toAddEquiv.toAddMonoidHom
  let e : GlobalRing (scheme)≃ₗ[ℚ]ℚ :=
    LinearEquiv.ofBijective f.toRatLinearMap (globalSectionsEquiv).bijective
  change Function.Bijective (algebraMap ℚ (GlobalRing (scheme)))
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
  simpa using e.finrank_eq

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveGlobalSections
