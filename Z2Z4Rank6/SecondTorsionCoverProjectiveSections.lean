import Z2Z4Rank6.SecondTorsionCoverProjectiveSectionsCore
import Z2Z4Rank6.SecondTorsionCoverProjectiveOverlap
namespace Z2Z4Rank6.SecondTorsionCoverProjectiveSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite
open SecondTorsionCoverProjective SecondTorsionCoverProjectiveCharts StructureSheafCohomology
variable (ε : Bool)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The (m ε)-chart sheaf restriction is the infinity restriction. -/
theorem mGammaRestriction :
    (mGammaIso ε).hom ≫ (scheme ε).presheaf.map (homOfLE inf_le_right : (zOpen ε)⊓(mOpen ε) ⟶ (mOpen ε)).op=
      CommRingCat.ofHom (SecondTorsionCoverOverlap.infinityRestriction ε).toRingHom ≫
        (overlapGammaIso ε).hom := by
  have hmap : CommRingCat.ofHom (mChartRingEquiv ε).symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom (mAway ε)=
      CommRingCat.ofHom (SecondTorsionCoverOverlap.infinityRestriction ε).toRingHom ≫
        CommRingCat.ofHom (R:=(ActualOverlap ε)) (S:=(HomogeneousOverlap ε)) (homogeneousOverlapEquiv ε).symm.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (mAway ε) ((mChartRingEquiv ε).symm x)=
      (homogeneousOverlapEquiv ε).symm ((SecondTorsionCoverOverlap.infinityRestriction ε) x)
    apply (homogeneousOverlapEquiv ε).injective
    have h := RingHom.congr_fun (mToActualOverlap_eq ε) ((mChartRingEquiv ε).symm x)
    change (homogeneousOverlapEquiv ε) ((mAway ε) ((mChartRingEquiv ε).symm x))=
      (SecondTorsionCoverOverlap.infinityRestriction ε) ((mChartRingEquiv ε) ((mChartRingEquiv ε).symm x)) at h
    simpa only [RingEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply] using h
  change (CommRingCat.ofHom (mChartRingEquiv ε).symm.toRingEquiv.toRingHom ≫
      (Proj.basicOpenIsoAway (grading ε) (m ε) (m_degree ε) (by decide : 0<1)).hom) ≫ _=
      CommRingCat.ofHom (SecondTorsionCoverOverlap.infinityRestriction ε).toRingHom ≫
        (CommRingCat.ofHom (R:=(ActualOverlap ε)) (S:=(HomogeneousOverlap ε)) (homogeneousOverlapEquiv ε).symm.toRingHom ≫ (homogeneousOverlapGammaIso ε).hom)
  rw [Category.assoc,←(mHomogeneousRestriction ε),←Category.assoc,hmap,Category.assoc]

theorem mRestrictionRing_apply (x : ↥Γ((scheme ε),(mOpen ε))) :
    (overlapSectionsRingEquiv ε) (((scheme ε).presheaf.map
      (homOfLE inf_le_right : (zOpen ε)⊓(mOpen ε) ⟶ (mOpen ε)).op) x)=
      (SecondTorsionCoverOverlap.infinityRestriction ε) ((mSectionsRingEquiv ε) x) := by
  have h := congrArg (fun f : CommRingCat.of (SecondTorsionCoverInfinity.CoordinateRing ε) ⟶
      Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) => f ((mSectionsRingEquiv ε) x)) (mGammaRestriction ε)
  change ((scheme ε).presheaf.map (homOfLE inf_le_right : (zOpen ε)⊓(mOpen ε) ⟶ (mOpen ε)).op)
      ((mGammaIso ε).hom ((mGammaIso ε).inv x))=
    (overlapGammaIso ε).hom ((SecondTorsionCoverOverlap.infinityRestriction ε) ((mGammaIso ε).inv x)) at h
  simp only [Iso.inv_hom_id_apply] at h
  change (overlapGammaIso ε).inv
    (((scheme ε).presheaf.map (homOfLE inf_le_right : (zOpen ε)⊓(mOpen ε) ⟶ (mOpen ε)).op) x)=
      (SecondTorsionCoverOverlap.infinityRestriction ε) ((mGammaIso ε).inv x)
  rw [h]
  exact Iso.hom_inv_id_apply _ _

theorem mRestriction_apply (x : sectionModule (scheme ε) (structureMap ε) (mOpen ε)) :
    (overlapSectionsEquiv ε) (restriction (scheme ε) (structureMap ε) (mOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_right x)=
      (SecondTorsionCoverOverlap.infinityRestriction ε) ((mSectionsEquiv ε) x) := (mRestrictionRing_apply ε) x

/-- Full linear-map diagram for the (m ε)-chart restriction. -/
theorem mRestriction_eq : (overlapSectionsEquiv ε).toLinearMap.comp
    (restriction (scheme ε) (structureMap ε) (mOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_right)=
      (SecondTorsionCoverOverlap.infinityRestriction ε).toLinearMap.comp (mSectionsEquiv ε).toLinearMap := by
  apply LinearMap.ext
  exact (mRestriction_apply ε)

end
end Z2Z4Rank6.SecondTorsionCoverProjectiveSections
