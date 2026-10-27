import Z2Z4Rank6.ThirdTwistCoverProjectiveSectionsCore
import Z2Z4Rank6.ThirdTwistCoverProjectiveOverlap
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts StructureSheafCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The (m)-chart sheaf restriction is the infinity restriction. -/
theorem mGammaRestriction :
    (mGammaIso).hom ≫ (scheme).presheaf.map (homOfLE inf_le_right : (zOpen)⊓(mOpen) ⟶ (mOpen)).op=
      CommRingCat.ofHom (ThirdTwistCoverOverlap.infinityRestriction).toRingHom ≫
        (overlapGammaIso).hom := by
  have hmap : CommRingCat.ofHom (mChartRingEquiv).symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom (mAway)=
      CommRingCat.ofHom (ThirdTwistCoverOverlap.infinityRestriction).toRingHom ≫
        CommRingCat.ofHom (R:=(ActualOverlap)) (S:=(HomogeneousOverlap)) (homogeneousOverlapEquiv).symm.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (mAway) ((mChartRingEquiv).symm x)=
      (homogeneousOverlapEquiv).symm ((ThirdTwistCoverOverlap.infinityRestriction) x)
    apply (homogeneousOverlapEquiv).injective
    have h := RingHom.congr_fun (mToActualOverlap_eq) ((mChartRingEquiv).symm x)
    change (homogeneousOverlapEquiv) ((mAway) ((mChartRingEquiv).symm x))=
      (ThirdTwistCoverOverlap.infinityRestriction) ((mChartRingEquiv) ((mChartRingEquiv).symm x)) at h
    simpa only [RingEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply] using h
  change (CommRingCat.ofHom (mChartRingEquiv).symm.toRingEquiv.toRingHom ≫
      (Proj.basicOpenIsoAway (grading) (m) (m_degree) (by decide : 0<1)).hom) ≫ _=
      CommRingCat.ofHom (ThirdTwistCoverOverlap.infinityRestriction).toRingHom ≫
        (CommRingCat.ofHom (R:=(ActualOverlap)) (S:=(HomogeneousOverlap)) (homogeneousOverlapEquiv).symm.toRingHom ≫ (homogeneousOverlapGammaIso).hom)
  rw [Category.assoc,←(mHomogeneousRestriction),←Category.assoc,hmap,Category.assoc]

theorem mRestrictionRing_apply (x : ↥Γ((scheme),(mOpen))) :
    (overlapSectionsRingEquiv) (((scheme).presheaf.map
      (homOfLE inf_le_right : (zOpen)⊓(mOpen) ⟶ (mOpen)).op) x)=
      (ThirdTwistCoverOverlap.infinityRestriction) ((mSectionsRingEquiv) x) := by
  have h := congrArg (fun f : CommRingCat.of (ThirdTwistCoverInfinity.CoordinateRing) ⟶
      Γ((scheme),(zOpen)⊓(mOpen)) => f ((mSectionsRingEquiv) x)) (mGammaRestriction)
  change ((scheme).presheaf.map (homOfLE inf_le_right : (zOpen)⊓(mOpen) ⟶ (mOpen)).op)
      ((mGammaIso).hom ((mGammaIso).inv x))=
    (overlapGammaIso).hom ((ThirdTwistCoverOverlap.infinityRestriction) ((mGammaIso).inv x)) at h
  simp only [Iso.inv_hom_id_apply] at h
  change (overlapGammaIso).inv
    (((scheme).presheaf.map (homOfLE inf_le_right : (zOpen)⊓(mOpen) ⟶ (mOpen)).op) x)=
      (ThirdTwistCoverOverlap.infinityRestriction) ((mGammaIso).inv x)
  rw [h]
  exact Iso.hom_inv_id_apply _ _

theorem mRestriction_apply (x : sectionModule (scheme) (structureMap) (mOpen)) :
    (overlapSectionsEquiv) (restriction (scheme) (structureMap) (mOpen) ((zOpen)⊓(mOpen)) inf_le_right x)=
      (ThirdTwistCoverOverlap.infinityRestriction) ((mSectionsEquiv) x) := (mRestrictionRing_apply) x

/-- Full linear-map diagram for the (m)-chart restriction. -/
theorem mRestriction_eq : (overlapSectionsEquiv).toLinearMap.comp
    (restriction (scheme) (structureMap) (mOpen) ((zOpen)⊓(mOpen)) inf_le_right)=
      (ThirdTwistCoverOverlap.infinityRestriction).toLinearMap.comp (mSectionsEquiv).toLinearMap := by
  apply LinearMap.ext
  exact (mRestriction_apply)

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveSections
