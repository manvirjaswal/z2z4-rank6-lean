module

public import Z2Z4Rank6.TorsionCoverProjectiveOverlapCore
public import Z2Z4Rank6.StructureSheafCohomology
public import Mathlib.Algebra.Module.LinearMap.Rat

@[expose] public section

/-!
# Structure-sheaf sections on the two projective charts

The chart and overlap rings below are the global sections on the
opens of Proj. Canonical Proj localization maps intertwine the
sheaf restrictions. Rational linearity uses the uniqueness of a
rational action on an additive group.
-/
namespace Z2Z4Rank6.TorsionCoverProjectiveSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory Opposite
open TorsionCoverProjective TorsionCoverProjectiveCharts
variable (ε : Bool)
open StructureSheafCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem z_degree : z ε∈grading ε 1 := coordinate_degree ε 3
theorem m_degree : m ε∈grading ε 1 := coordinate_degree ε 0

/-- The homogeneous overlap has degree two. -/
theorem overlap_degree : (z ε)*(m ε)∈(grading ε) 2 :=
  SetLike.mul_mem_graded (z_degree ε) (m_degree ε)

theorem overlapOpen_eq : Proj.basicOpen (grading ε) ((z ε)*(m ε))=(zOpen ε)⊓(mOpen ε) :=
  Proj.basicOpen_mul (grading ε) (z ε) (m ε)

/-- Canonical change from the standard homogeneous overlap open to the intersection. -/
def overlapSectionTransport : Γ((scheme ε),Proj.basicOpen (grading ε) ((z ε)*(m ε))) ≅ Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) :=
  (scheme ε).presheaf.mapIso (eqToIso (overlapOpen_eq ε)).symm.op

/-- Homogeneous localization gives the structure-sheaf overlap sections. -/
def homogeneousOverlapGammaIso : CommRingCat.of (HomogeneousOverlap ε) ≅ Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) :=
  Proj.basicOpenIsoAway (grading ε) ((z ε)*(m ε)) (overlap_degree ε) (by decide : 0<2) ≪≫
    (overlapSectionTransport ε)

/-- Affine coordinate ring to sections on (z ε)≠0. -/
def zGammaIso : CommRingCat.of (TorsionCoverAffine.CoordinateRing ε) ≅ Γ((scheme ε),(zOpen ε)) :=
  (zChartRingEquiv ε).symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway (grading ε) (z ε) (z_degree ε) (by decide : 0<1)

/-- Infinity coordinate ring to sections on (m ε)≠0. -/
def mGammaIso : CommRingCat.of (TorsionCoverInfinity.CoordinateRing ε) ≅ Γ((scheme ε),(mOpen ε)) :=
  (mChartRingEquiv ε).symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway (grading ε) (m ε) (m_degree ε) (by decide : 0<1)

/-- Affine localization to sections on the chart intersection. -/
def overlapGammaIso : CommRingCat.of (ActualOverlap ε) ≅ Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) :=
  (homogeneousOverlapEquiv ε).symm.toCommRingCatIso ≪≫ (homogeneousOverlapGammaIso ε)

def zSectionsRingEquiv : ↥Γ((scheme ε),(zOpen ε)) ≃+* (TorsionCoverAffine.CoordinateRing ε) :=
  (zGammaIso ε).symm.commRingCatIsoToRingEquiv

def mSectionsRingEquiv : ↥Γ((scheme ε),(mOpen ε)) ≃+* (TorsionCoverInfinity.CoordinateRing ε) :=
  (mGammaIso ε).symm.commRingCatIsoToRingEquiv

def overlapSectionsRingEquiv : ↥Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) ≃+* (ActualOverlap ε) :=
  (overlapGammaIso ε).symm.commRingCatIsoToRingEquiv

/-- Every additive equivalence between rational modules is rational linear. -/
def addEquivToRatLinearEquiv {M N : Type*} [AddCommGroup M] [Module ℚ M]
    [AddCommGroup N] [Module ℚ N] (e : M ≃+ N) : M ≃ₗ[ℚ] N :=
  {e with map_smul' := map_rat_smul e.toAddMonoidHom}

/-- The (z ε)-chart identification with its rational structure-sheaf action. -/
def zSectionsEquiv : sectionModule (scheme ε) (structureMap ε) (zOpen ε) ≃ₗ[ℚ]
    (TorsionCoverAffine.CoordinateRing ε) := addEquivToRatLinearEquiv (zSectionsRingEquiv ε).toAddEquiv

/-- The (m ε)-chart identification with its rational structure-sheaf action. -/
def mSectionsEquiv : sectionModule (scheme ε) (structureMap ε) (mOpen ε) ≃ₗ[ℚ]
    (TorsionCoverInfinity.CoordinateRing ε) := addEquivToRatLinearEquiv (mSectionsRingEquiv ε).toAddEquiv

/-- The overlap identification with its rational structure-sheaf action. -/
def overlapSectionsEquiv : sectionModule (scheme ε) (structureMap ε) ((zOpen ε)⊓(mOpen ε)) ≃ₗ[ℚ]
    (ActualOverlap ε) := addEquivToRatLinearEquiv (overlapSectionsRingEquiv ε).toAddEquiv

/-- Canonical Proj restrictions from the (z ε)-chart are the homogeneous localization maps. -/
theorem zHomogeneousRestriction :
    CommRingCat.ofHom (zAway ε) ≫ (homogeneousOverlapGammaIso ε).hom=
      (Proj.basicOpenIsoAway (grading ε) (z ε) (z_degree ε) (by decide : 0<1)).hom ≫
        (scheme ε).presheaf.map (homOfLE inf_le_left : (zOpen ε)⊓(mOpen ε) ⟶ (zOpen ε)).op := by
  rw [homogeneousOverlapGammaIso,Iso.trans_hom,←Category.assoc]
  change (CommRingCat.ofHom (zAway ε) ≫ Proj.awayToSection (grading ε) ((z ε)*(m ε))) ≫
    (overlapSectionTransport ε).hom=Proj.awayToSection (grading ε) (z ε) ≫ _
  dsimp only [scheme,zAway]
  rw [Proj.awayMap_awayToSection (grading ε) (m_degree ε) (rfl : (z ε)*(m ε)=(z ε)*(m ε))]
  rw [Category.assoc]
  congr 1

/-- Canonical Proj restrictions from the (m ε)-chart are the other homogeneous localization map. -/
theorem mHomogeneousRestriction :
    CommRingCat.ofHom (mAway ε) ≫ (homogeneousOverlapGammaIso ε).hom=
      (Proj.basicOpenIsoAway (grading ε) (m ε) (m_degree ε) (by decide : 0<1)).hom ≫
        (scheme ε).presheaf.map (homOfLE inf_le_right : (zOpen ε)⊓(mOpen ε) ⟶ (mOpen ε)).op := by
  rw [homogeneousOverlapGammaIso,Iso.trans_hom,←Category.assoc]
  change (CommRingCat.ofHom (mAway ε) ≫ Proj.awayToSection (grading ε) ((z ε)*(m ε))) ≫
    (overlapSectionTransport ε).hom=Proj.awayToSection (grading ε) (m ε) ≫ _
  dsimp only [scheme,mAway]
  rw [Proj.awayMap_awayToSection (grading ε) (z_degree ε) (mul_comm (z ε) (m ε))]
  rw [Category.assoc]
  congr 1

/-- The (z ε)-chart sheaf restriction is the affine localization map. -/
theorem zGammaRestriction :
    (zGammaIso ε).hom ≫ (scheme ε).presheaf.map (homOfLE inf_le_left : (zOpen ε)⊓(mOpen ε) ⟶ (zOpen ε)).op=
      CommRingCat.ofHom (algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)) ≫
        (overlapGammaIso ε).hom := by
  have hmap : CommRingCat.ofHom (zChartRingEquiv ε).symm.toRingEquiv.toRingHom ≫
      CommRingCat.ofHom (zAway ε)=
      CommRingCat.ofHom (algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)) ≫
        CommRingCat.ofHom (R:=(ActualOverlap ε)) (S:=(HomogeneousOverlap ε)) (homogeneousOverlapEquiv ε).symm.toRingHom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change (zAway ε) ((zChartRingEquiv ε).symm x)=
      (homogeneousOverlapEquiv ε).symm (algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε) x)
    apply (homogeneousOverlapEquiv ε).injective
    simp only [(homogeneousOverlapEquiv_zAway ε),AlgEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  change (CommRingCat.ofHom (zChartRingEquiv ε).symm.toRingEquiv.toRingHom ≫
      (Proj.basicOpenIsoAway (grading ε) (z ε) (z_degree ε) (by decide : 0<1)).hom) ≫ _=
      CommRingCat.ofHom (algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)) ≫
        (CommRingCat.ofHom (R:=(ActualOverlap ε)) (S:=(HomogeneousOverlap ε)) (homogeneousOverlapEquiv ε).symm.toRingHom ≫ (homogeneousOverlapGammaIso ε).hom)
  rw [Category.assoc,←(zHomogeneousRestriction ε),←Category.assoc,hmap,Category.assoc]

theorem zRestrictionRing_apply (x : ↥Γ((scheme ε),(zOpen ε))) :
    (overlapSectionsRingEquiv ε) (((scheme ε).presheaf.map
      (homOfLE inf_le_left : (zOpen ε)⊓(mOpen ε) ⟶ (zOpen ε)).op) x)=
      algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε) ((zSectionsRingEquiv ε) x) := by
  have h := congrArg (fun f : CommRingCat.of (TorsionCoverAffine.CoordinateRing ε) ⟶
      Γ((scheme ε),(zOpen ε)⊓(mOpen ε)) => f ((zSectionsRingEquiv ε) x)) (zGammaRestriction ε)
  change ((scheme ε).presheaf.map (homOfLE inf_le_left : (zOpen ε)⊓(mOpen ε) ⟶ (zOpen ε)).op)
      ((zGammaIso ε).hom ((zGammaIso ε).inv x))=
    (overlapGammaIso ε).hom (algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε) ((zGammaIso ε).inv x)) at h
  simp only [Iso.inv_hom_id_apply] at h
  change (overlapGammaIso ε).inv
    (((scheme ε).presheaf.map (homOfLE inf_le_left : (zOpen ε)⊓(mOpen ε) ⟶ (zOpen ε)).op) x)=
      algebraMap (TorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε) ((zGammaIso ε).inv x)
  rw [h]
  exact Iso.hom_inv_id_apply _ _

theorem zRestriction_apply (x : sectionModule (scheme ε) (structureMap ε) (zOpen ε)) :
    (overlapSectionsEquiv ε) (restriction (scheme ε) (structureMap ε) (zOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_left x)=
      (TorsionCoverOverlap.affineRestriction ε) ((zSectionsEquiv ε) x) := (zRestrictionRing_apply ε) x

/-- Full linear-map diagram for the (z ε)-chart restriction. -/
theorem zRestriction_eq : (overlapSectionsEquiv ε).toLinearMap.comp
    (restriction (scheme ε) (structureMap ε) (zOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_left)=
      (TorsionCoverOverlap.affineRestriction ε).comp (zSectionsEquiv ε).toLinearMap := by
  apply LinearMap.ext
  exact (zRestriction_apply ε)


end
end Z2Z4Rank6.TorsionCoverProjectiveSections
