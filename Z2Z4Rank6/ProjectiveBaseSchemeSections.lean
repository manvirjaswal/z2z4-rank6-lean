import Z2Z4Rank6.ProjectiveBaseSchemeOverlap
import Z2Z4Rank6.StructureSheafCohomology
import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Structure-sheaf sections on the two projective charts

The chart and overlap rings below are the global sections on the
opens of Proj. Canonical Proj localization maps intertwine the
sheaf restrictions. Rational linearity uses the uniqueness of a
rational action on an additive group.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite
open ProjectiveBaseScheme ProjectiveBaseSchemeCharts
open StructureSheafCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The homogeneous overlap has degree two. -/
theorem overlap_degree : z*m∈grading 2 :=
  SetLike.mul_mem_graded (coordinate_degree 3) (coordinate_degree 0)

theorem overlapOpen_eq : Proj.basicOpen grading (z*m)=zOpen⊓mOpen :=
  Proj.basicOpen_mul grading z m

/-- Canonical change from the standard homogeneous overlap open to the intersection. -/
def overlapSectionTransport : Γ(scheme,Proj.basicOpen grading (z*m)) ≅ Γ(scheme,zOpen⊓mOpen) :=
  scheme.presheaf.mapIso (eqToIso overlapOpen_eq).symm.op

/-- Homogeneous localization gives the structure-sheaf overlap sections. -/
def homogeneousOverlapGammaIso : CommRingCat.of HomogeneousOverlap ≅ Γ(scheme,zOpen⊓mOpen) :=
  Proj.basicOpenIsoAway grading (z*m) overlap_degree (by decide : 0<2) ≪≫
    overlapSectionTransport

/-- Affine coordinate ring to sections on z≠0. -/
def zGammaIso : CommRingCat.of AffineBaseScheme.CoordinateRing ≅ Γ(scheme,zOpen) :=
  zChartRingEquiv.symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway grading z (coordinate_degree 3) (by decide : 0<1)

/-- Infinity coordinate ring to sections on m≠0. -/
def mGammaIso : CommRingCat.of InfinityCoordinateRing ≅ Γ(scheme,mOpen) :=
  mChartRingEquiv.symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway grading m (coordinate_degree 0) (by decide : 0<1)

/-- Affine localization to sections on the chart intersection. -/
def overlapGammaIso : CommRingCat.of ActualOverlap ≅ Γ(scheme,zOpen⊓mOpen) :=
  homogeneousOverlapEquiv.symm.toCommRingCatIso ≪≫ homogeneousOverlapGammaIso

def zSectionsRingEquiv : ↥Γ(scheme,zOpen) ≃+* AffineBaseScheme.CoordinateRing :=
  zGammaIso.symm.commRingCatIsoToRingEquiv

def mSectionsRingEquiv : ↥Γ(scheme,mOpen) ≃+* InfinityCoordinateRing :=
  mGammaIso.symm.commRingCatIsoToRingEquiv

def overlapSectionsRingEquiv : ↥Γ(scheme,zOpen⊓mOpen) ≃+* ActualOverlap :=
  overlapGammaIso.symm.commRingCatIsoToRingEquiv

/-- Every additive equivalence between rational modules is rational linear. -/
def addEquivToRatLinearEquiv {M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] (e : M ≃+ N) : M ≃ₗ[ℚ] N :=
  {e with map_smul' := map_rat_smul e.toAddMonoidHom}

/-- The z-chart identification with its rational structure-sheaf action. -/
def zSectionsEquiv : sectionModule scheme structureMap zOpen ≃ₗ[ℚ]
    AffineBaseScheme.CoordinateRing := addEquivToRatLinearEquiv zSectionsRingEquiv.toAddEquiv

/-- The m-chart identification with its rational structure-sheaf action. -/
def mSectionsEquiv : sectionModule scheme structureMap mOpen ≃ₗ[ℚ]
    InfinityCoordinateRing := addEquivToRatLinearEquiv mSectionsRingEquiv.toAddEquiv

/-- The overlap identification with its rational structure-sheaf action. -/
def overlapSectionsEquiv : sectionModule scheme structureMap (zOpen⊓mOpen) ≃ₗ[ℚ]
    ActualOverlap := addEquivToRatLinearEquiv overlapSectionsRingEquiv.toAddEquiv

/-- Canonical Proj restrictions from the z-chart are the homogeneous localization maps. -/
theorem zHomogeneousRestriction :
    CommRingCat.ofHom zAway ≫ homogeneousOverlapGammaIso.hom=
      (Proj.basicOpenIsoAway grading z (coordinate_degree 3) (by decide : 0<1)).hom ≫
        scheme.presheaf.map (homOfLE inf_le_left : zOpen⊓mOpen ⟶ zOpen).op := by
  rw [homogeneousOverlapGammaIso,Iso.trans_hom,←Category.assoc]
  change (CommRingCat.ofHom zAway ≫ Proj.awayToSection grading (z*m)) ≫
    overlapSectionTransport.hom=Proj.awayToSection grading z ≫ _
  dsimp only [scheme,zAway]
  rw [Proj.awayMap_awayToSection grading (coordinate_degree 0) (rfl : z*m=z*m)]
  rw [Category.assoc]
  congr 1

/-- Canonical Proj restrictions from the m-chart are the other homogeneous localization map. -/
theorem mHomogeneousRestriction :
    CommRingCat.ofHom mAway ≫ homogeneousOverlapGammaIso.hom=
      (Proj.basicOpenIsoAway grading m (coordinate_degree 0) (by decide : 0<1)).hom ≫
        scheme.presheaf.map (homOfLE inf_le_right : zOpen⊓mOpen ⟶ mOpen).op := by
  rw [homogeneousOverlapGammaIso,Iso.trans_hom,←Category.assoc]
  change (CommRingCat.ofHom mAway ≫ Proj.awayToSection grading (z*m)) ≫
    overlapSectionTransport.hom=Proj.awayToSection grading m ≫ _
  dsimp only [scheme,mAway]
  rw [Proj.awayMap_awayToSection grading (coordinate_degree 3) (mul_comm z m)]
  rw [Category.assoc]
  congr 1

/-- The z-chart sheaf restriction is the affine localization map. -/
theorem zGammaRestriction :
    zGammaIso.hom ≫ scheme.presheaf.map (homOfLE inf_le_left : zOpen⊓mOpen ⟶ zOpen).op=
      CommRingCat.ofHom (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap) ≫
        overlapGammaIso.hom := by
  have hmap : CommRingCat.ofHom zChartRingEquiv.symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom zAway=
      CommRingCat.ofHom (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap) ≫
        CommRingCat.ofHom (R:=ActualOverlap) (S:=HomogeneousOverlap) homogeneousOverlapEquiv.symm.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change zAway (zChartRingEquiv.symm x)=
      homogeneousOverlapEquiv.symm (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap x)
    apply homogeneousOverlapEquiv.injective
    simp only [homogeneousOverlapEquiv_zAway,AlgEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  change (CommRingCat.ofHom zChartRingEquiv.symm.toRingEquiv.toRingHom ≫
      (Proj.basicOpenIsoAway grading z (coordinate_degree 3) (by decide : 0<1)).hom) ≫ _=
      CommRingCat.ofHom (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap) ≫
        (CommRingCat.ofHom (R:=ActualOverlap) (S:=HomogeneousOverlap) homogeneousOverlapEquiv.symm.toRingHom ≫ homogeneousOverlapGammaIso.hom)
  rw [Category.assoc,←zHomogeneousRestriction,←Category.assoc,hmap,Category.assoc]

/-- The m-chart sheaf restriction is the infinity restriction. -/
theorem mGammaRestriction :
    mGammaIso.hom ≫ scheme.presheaf.map (homOfLE inf_le_right : zOpen⊓mOpen ⟶ mOpen).op=
      CommRingCat.ofHom AffineBaseFunctionFieldIso.infinityRestriction.toRingHom ≫
        overlapGammaIso.hom := by
  have hmap : CommRingCat.ofHom mChartRingEquiv.symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom mAway=
      CommRingCat.ofHom AffineBaseFunctionFieldIso.infinityRestriction.toRingHom ≫
        CommRingCat.ofHom (R:=ActualOverlap) (S:=HomogeneousOverlap) homogeneousOverlapEquiv.symm.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change mAway (mChartRingEquiv.symm x)=
      homogeneousOverlapEquiv.symm (AffineBaseFunctionFieldIso.infinityRestriction x)
    apply homogeneousOverlapEquiv.injective
    have h := RingHom.congr_fun mToActualOverlap_eq (mChartRingEquiv.symm x)
    change homogeneousOverlapEquiv (mAway (mChartRingEquiv.symm x))=
      AffineBaseFunctionFieldIso.infinityRestriction (mChartRingEquiv (mChartRingEquiv.symm x)) at h
    simpa only [RingEquiv.apply_symm_apply,AlgEquiv.apply_symm_apply] using h
  change (CommRingCat.ofHom mChartRingEquiv.symm.toRingEquiv.toRingHom ≫
      (Proj.basicOpenIsoAway grading m (coordinate_degree 0) (by decide : 0<1)).hom) ≫ _=
      CommRingCat.ofHom AffineBaseFunctionFieldIso.infinityRestriction.toRingHom ≫
        (CommRingCat.ofHom (R:=ActualOverlap) (S:=HomogeneousOverlap) homogeneousOverlapEquiv.symm.toRingHom ≫ homogeneousOverlapGammaIso.hom)
  rw [Category.assoc,←mHomogeneousRestriction,←Category.assoc,hmap,Category.assoc]

theorem zRestrictionRing_apply (x : ↥Γ(scheme,zOpen)) :
    overlapSectionsRingEquiv ((scheme.presheaf.map
      (homOfLE inf_le_left : zOpen⊓mOpen ⟶ zOpen).op) x)=
      algebraMap AffineBaseScheme.CoordinateRing ActualOverlap (zSectionsRingEquiv x) := by
  have h := congrArg (fun f : CommRingCat.of AffineBaseScheme.CoordinateRing ⟶
      Γ(scheme,zOpen⊓mOpen) => f (zSectionsRingEquiv x)) zGammaRestriction
  change (scheme.presheaf.map (homOfLE inf_le_left : zOpen⊓mOpen ⟶ zOpen).op)
      (zGammaIso.hom (zGammaIso.inv x))=
    overlapGammaIso.hom (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap (zGammaIso.inv x)) at h
  simp only [Iso.inv_hom_id_apply] at h
  change overlapGammaIso.inv
    ((scheme.presheaf.map (homOfLE inf_le_left : zOpen⊓mOpen ⟶ zOpen).op) x)=
      algebraMap AffineBaseScheme.CoordinateRing ActualOverlap (zGammaIso.inv x)
  rw [h]
  exact Iso.hom_inv_id_apply _ _

theorem mRestrictionRing_apply (x : ↥Γ(scheme,mOpen)) :
    overlapSectionsRingEquiv ((scheme.presheaf.map
      (homOfLE inf_le_right : zOpen⊓mOpen ⟶ mOpen).op) x)=
      AffineBaseFunctionFieldIso.infinityRestriction (mSectionsRingEquiv x) := by
  have h := congrArg (fun f : CommRingCat.of InfinityCoordinateRing ⟶
      Γ(scheme,zOpen⊓mOpen) => f (mSectionsRingEquiv x)) mGammaRestriction
  change (scheme.presheaf.map (homOfLE inf_le_right : zOpen⊓mOpen ⟶ mOpen).op)
      (mGammaIso.hom (mGammaIso.inv x))=
    overlapGammaIso.hom (AffineBaseFunctionFieldIso.infinityRestriction (mGammaIso.inv x)) at h
  simp only [Iso.inv_hom_id_apply] at h
  change overlapGammaIso.inv
    ((scheme.presheaf.map (homOfLE inf_le_right : zOpen⊓mOpen ⟶ mOpen).op) x)=
      AffineBaseFunctionFieldIso.infinityRestriction (mGammaIso.inv x)
  rw [h]
  exact Iso.hom_inv_id_apply _ _

theorem zRestriction_apply (x : sectionModule scheme structureMap zOpen) :
    overlapSectionsEquiv (restriction scheme structureMap zOpen (zOpen⊓mOpen) inf_le_left x)=
      AffineBaseFunctionFieldIso.affineRestriction (zSectionsEquiv x) := zRestrictionRing_apply x

theorem mRestriction_apply (x : sectionModule scheme structureMap mOpen) :
    overlapSectionsEquiv (restriction scheme structureMap mOpen (zOpen⊓mOpen) inf_le_right x)=
      AffineBaseFunctionFieldIso.infinityRestriction (mSectionsEquiv x) := mRestrictionRing_apply x

/-- Full linear-map diagram for the z-chart restriction. -/
theorem zRestriction_eq : overlapSectionsEquiv.toLinearMap.comp
    (restriction scheme structureMap zOpen (zOpen⊓mOpen) inf_le_left)=
      AffineBaseFunctionFieldIso.affineRestriction.comp zSectionsEquiv.toLinearMap := by
  apply LinearMap.ext
  exact zRestriction_apply

/-- Full linear-map diagram for the m-chart restriction. -/
theorem mRestriction_eq : overlapSectionsEquiv.toLinearMap.comp
    (restriction scheme structureMap mOpen (zOpen⊓mOpen) inf_le_right)=
      AffineBaseFunctionFieldIso.infinityRestriction.toLinearMap.comp mSectionsEquiv.toLinearMap := by
  apply LinearMap.ext
  exact mRestriction_apply

end
end Z2Z4Rank6.ProjectiveBaseSchemeSections
