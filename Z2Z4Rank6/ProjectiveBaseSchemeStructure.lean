module

public import Z2Z4Rank6.ProjectiveBaseSchemeInfinity
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

@[expose] public section

/-!
# Rational structure map of the projective base

Jaswal, DOI 10.5281/zenodo.23437117, Section 3. The degree-zero ring
of the homogeneous coordinate algebra is Q. The Proj structure
map is consequently a proper Q-scheme morphism. Its two affine
charts have exactly the displayed affine Q-structure maps.
-/
namespace Z2Z4Rank6.ProjectiveBaseScheme
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseSchemeCharts
set_option backward.isDefEq.respectTransparency false

instance coordinateRing_nontrivial : Nontrivial CoordinateRing := atZOne.toRingHom.domain_nontrivial

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

/-- Q-scheme structure on the homogeneous intersection. -/
def structureMap : scheme ⟶ Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))

instance coordinateRing_finiteType : Algebra.FiniteType (grading 0) CoordinateRing := by
  let : Algebra.FiniteType ℚ CoordinateRing := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ (grading 0) CoordinateRing

/-- The projective intersection has a proved proper structure map over Q. -/
instance structureMap_proper : IsProper structureMap := by
  have hIso : IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))) := by
    change IsIso (Scheme.Spec.mapIso degreeZeroEquiv.toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

def chartInclusion (k : Fin 4) : Spec (CommRingCat.of (ChartRing k)) ⟶ scheme :=
  Proj.awayι grading (coordinate k) (coordinate_degree k) (by decide : 0<1)

/-- Every homogeneous coordinate chart carries the natural rational structure. -/
theorem chartInclusion_structureMap (k : Fin 4) :
    chartInclusion k ≫ structureMap=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartRing k))) := by
  dsimp only [chartInclusion,structureMap,scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero]
  rw [←Spec.map_comp]
  rfl

/-- Compatibility of the z-chart identification with the Q-structure maps. -/
theorem zChartSchemeIso_structureMap :
    zChartSchemeIso.hom ≫ AffineBaseScheme.structureMap=zOpen.ι ≫ structureMap := by
  apply (cancel_epi zChartIso.inv).mp
  rw [←Category.assoc,←Category.assoc]
  change (zChartIso.inv ≫ zChartSchemeIso.hom) ≫ AffineBaseScheme.structureMap=
    chartInclusion 3 ≫ structureMap
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom zChartRingEquiv.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ AffineBaseScheme.CoordinateRing))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val (zChartRingEquiv.symm.commutes q)

/-- Compatibility of the m-chart identification with its Q-structure map. -/
theorem mChartSchemeIso_structureMap :
    mChartSchemeIso.hom ≫ infinityStructureMap=mOpen.ι ≫ structureMap := by
  apply (cancel_epi mChartIso.inv).mp
  rw [←Category.assoc,←Category.assoc]
  change (mChartIso.inv ≫ mChartSchemeIso.hom) ≫ infinityStructureMap=
    chartInclusion 0 ≫ structureMap
  rw [chartInclusion_structureMap]
  rw [mChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom mChartRingEquiv.symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ InfinityCoordinateRing))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val (mChartRingEquiv.symm.commutes q)

end
end Z2Z4Rank6.ProjectiveBaseScheme
