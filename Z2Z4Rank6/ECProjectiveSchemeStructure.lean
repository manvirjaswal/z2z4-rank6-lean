module

public import Z2Z4Rank6.ECProjectiveSchemeCharts
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

@[expose] public section

/-!
# Rational structure map of the printed projective cubic

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1. The degree-zero ring
of the homogeneous coordinate algebra is Q. The Proj structure
map is consequently a proper Q-scheme morphism. Its two affine
charts have exactly the displayed affine Q-structure maps.
-/
namespace Z2Z4Rank6.ECProjectiveScheme
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ECProjectiveSchemeCharts
set_option backward.isDefEq.respectTransparency false


instance gradeZero_nontrivial : Nontrivial (grading 0) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have he : (0:CoordinateRing)=1 := congrArg Subtype.val h
  exact zero_ne_one he

instance gradeZero_scalarTower : IsScalarTower ℚ (grading 0) CoordinateRing :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=grading 0) (A:=CoordinateRing) rfl

/-- The degree-zero coefficient ring is exactly Q, with its algebra map. -/
def degreeZeroEquiv : ℚ ≃+* grading 0 :=
  RingEquiv.ofBijective (algebraMap ℚ (grading 0))
    ⟨(algebraMap ℚ (grading 0)).injective,fun r => by
      obtain ⟨q,hq⟩ := degreeZero_eq_rat r
      exact ⟨q,hq.symm⟩⟩

/-- Q-scheme structure on the projective cubic. -/
def structureMap : scheme ⟶ Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))

instance coordinateRing_finiteType : Algebra.FiniteType (grading 0) CoordinateRing := by
  let : Algebra.FiniteType ℚ CoordinateRing := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ (grading 0) CoordinateRing

/-- The projective cubic has a proved proper structure map over Q. -/
instance structureMap_proper : IsProper structureMap := by
  have hIso : IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))) := by
    change IsIso (Scheme.Spec.mapIso degreeZeroEquiv.toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

def chartInclusion (k : Fin 3) : Spec (CommRingCat.of (ChartRing k)) ⟶ scheme :=
  Proj.awayι grading (coordinate k) (coordinate_degree k) (by decide : 0<1)

/-- Every homogeneous coordinate chart carries the natural rational structure. -/
theorem chartInclusion_structureMap (k : Fin 3) :
    chartInclusion k ≫ structureMap=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartRing k))) := by
  dsimp only [chartInclusion,structureMap,scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero]
  rw [←Spec.map_comp]
  rfl

/-- Compatibility of the z-chart identification with the Q-structure maps. -/
theorem zChartSchemeIso_structureMap :
    zChartSchemeIso.hom ≫ ECProjectiveSchemeAffine.structureMap=zOpen.ι ≫ structureMap := by
  apply (cancel_epi zChartIso.inv).mp
  rw [←Category.assoc,←Category.assoc]
  change (zChartIso.inv ≫ zChartSchemeIso.hom) ≫ ECProjectiveSchemeAffine.structureMap=
    chartInclusion 2 ≫ structureMap
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom zChartRingEquiv.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ECProjectiveSchemeAffine.CoordinateRing))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val (zChartRingEquiv.symm.commutes q)

/-- Chart evaluation at the homogeneous infinity coordinates (0,1,0). -/
def infinityChartEvaluation : ChartRing 1→ₐ[ℚ]ℚ :=
  rationalAlgHom ((Localization.awayLift infinityEvaluation.toRingHom y (by simp [y])).comp
    (algebraMap (ChartRing 1) (LocalizedRing 1)))

@[simp] theorem infinityChartEvaluation_ratio (i:Fin 3) :
    infinityChartEvaluation (ratio 1 i)=![(0:ℚ),1,0] i := by
  change Localization.awayLift infinityEvaluation.toRingHom y (by simp [y]) (ratio 1 i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift infinityEvaluation.toRingHom y (by simp [y])
      (inverseCoordinate 1)=1 := by
    have h := congrArg (Localization.awayLift infinityEvaluation.toRingHom y (by simp [y]))
      (coordinate_mul_inverse 1)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change infinityEvaluation (coordinate 1)*Localization.awayLift infinityEvaluation.toRingHom y _
      (inverseCoordinate 1)=1 at h
    simpa using h
  rw [hi,mul_one]
  exact infinityEvaluation_coordinate i

/-- Spec Q-valued point at infinity on the projective cubic. -/
def infinityPoint : Spec (CommRingCat.of ℚ)⟶scheme :=
  Spec.map (CommRingCat.ofHom infinityChartEvaluation.toRingHom) ≫ chartInclusion 1

theorem infinityPoint_over : infinityPoint≫structureMap=𝟙 (Spec (CommRingCat.of ℚ)) := by
  rw [infinityPoint,Category.assoc,chartInclusion_structureMap,←Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℚ (ChartRing 1)) ≫
      CommRingCat.ofHom infinityChartEvaluation.toRingHom=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [h,Spec.map_id]

/-- The infinity point lies outside the displayed affine chart. -/
theorem infinityPoint_not_mem_zOpen (p:Spec (CommRingCat.of ℚ)) :
    infinityPoint p∉zOpen := by
  have hpre : chartInclusion 1 ⁻¹ᵁ zOpen=PrimeSpectrum.basicOpen (ratio 1 2) := by
    change Proj.awayι grading y (coordinate_degree 1) (by decide:0<1) ⁻¹ᵁ
      Proj.basicOpen grading z=_
    rw [Proj.awayι_preimage_basicOpen grading (coordinate_degree 1) (by decide:0<1)
      (coordinate_degree 2) (by decide:0<1)]
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.Away.isLocalizationElem,HomogeneousLocalization.Away.val_mk,
      ratio,pow_one]
  change (Spec.map (CommRingCat.ofHom infinityChartEvaluation.toRingHom)) p∉
    chartInclusion 1 ⁻¹ᵁ zOpen
  rw [hpre]
  change ¬infinityChartEvaluation (ratio 1 2)∉p.asIdeal
  simp

end
end Z2Z4Rank6.ECProjectiveScheme
