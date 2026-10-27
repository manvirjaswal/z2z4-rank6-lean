module

public import Z2Z4Rank6.ECProjectiveSchemeStructure

@[expose] public section

/-! The Y-chart of the printed Weierstrass cubic, including infinity.
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
The coordinate order is (X/Y,Z/Y).
-/
namespace Z2Z4Rank6.ECProjectiveSchemeInfinity
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
open ECProjectiveScheme ECProjectiveSchemeCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev PolynomialRing := MvPolynomial (Fin 2) ℚ
def relation (_:Fin 1) : PolynomialRing :=
  MvPolynomial.X 1-MvPolynomial.X 0^3-MvPolynomial.X 0^2*MvPolynomial.X 1+
    137620*MvPolynomial.X 0*MvPolynomial.X 1^2+10504000*MvPolynomial.X 1^3
def definingIdeal : Ideal PolynomialRing := Ideal.span (Set.range relation)
abbrev CoordinateRing := PolynomialRing⧸definingIdeal
def x : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 0)
def z : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 1)
def presentation : Algebra.Presentation ℚ CoordinateRing (Fin 2) (Fin 1) :=
  Algebra.Presentation.naive (v:=relation)
instance finitePresentation : Algebra.FinitePresentation ℚ CoordinateRing :=
  presentation.finitePresentation_of_isFinite

theorem equation : z=x^3+x^2*z-137620*x*z^2-10504000*z^3 := by
  have h : Ideal.Quotient.mk definingIdeal (relation 0)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0,rfl⟩)
  simp only [relation,map_sub,map_add,map_pow,map_mul,map_ofNat] at h
  change z-x^3-x^2*z+137620*x*z^2+10504000*z^3=0 at h
  linear_combination h

def scheme : Scheme := Spec (CommRingCat.of CoordinateRing)
def structureMap : scheme⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ CoordinateRing))

def atYOne : ECProjectiveScheme.CoordinateRing→ₐ[ℚ]CoordinateRing :=
  Ideal.Quotient.liftₐ ECProjectiveScheme.definingIdeal (MvPolynomial.aeval ![x,1,z]) (by
    have hker : ECProjectiveScheme.definingIdeal≤RingHom.ker
        (MvPolynomial.aeval ![x,1,z]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p (rfl:p=ECProjectiveScheme.relation)
      change (MvPolynomial.aeval _) ECProjectiveScheme.relation=0
      norm_num [ECProjectiveScheme.relation]
      norm_num only [map_ofNat]
      linear_combination equation
    intro p hp
    exact hker hp)

@[simp] theorem atYOne_coordinate (i:Fin 3) : atYOne (coordinate i)=![x,1,z] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity : ChartRing 1→ₐ[ℚ]CoordinateRing :=
  rationalAlgHom ((Localization.awayLift atYOne.toRingHom ECProjectiveScheme.y
    (by simp [ECProjectiveScheme.y])).comp (algebraMap (ChartRing 1) (LocalizedRing 1)))

@[simp] theorem chartToInfinity_ratio (i:Fin 3) : chartToInfinity (ratio 1 i)=![x,1,z] i := by
  change Localization.awayLift atYOne.toRingHom ECProjectiveScheme.y
    (by simp [ECProjectiveScheme.y]) (ratio 1 i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift atYOne.toRingHom ECProjectiveScheme.y
      (by simp [ECProjectiveScheme.y]) (inverseCoordinate 1)=1 := by
    have h := congrArg (Localization.awayLift atYOne.toRingHom ECProjectiveScheme.y
      (by simp [ECProjectiveScheme.y])) (coordinate_mul_inverse 1)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atYOne (coordinate 1)*Localization.awayLift atYOne.toRingHom ECProjectiveScheme.y _
      (inverseCoordinate 1)=1 at h
    simpa using h
  rw [hi,mul_one]
  exact atYOne_coordinate i

def infinityToChart : CoordinateRing→ₐ[ℚ]ChartRing 1 :=
  Ideal.Quotient.liftₐ definingIdeal (MvPolynomial.aeval ![ratio 1 0,ratio 1 2]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![ratio 1 0,ratio 1 2]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval _) (relation i)=0
      simp [relation]
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.val_add,HomogeneousLocalization.val_sub,
        HomogeneousLocalization.val_pow,HomogeneousLocalization.val_mul,
        HomogeneousLocalization.val_zero,ratio_val]
      norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
      have h := congrArg (algebraMap ECProjectiveScheme.CoordinateRing (LocalizedRing 1)) cubic_equation
      simp only [map_add,map_sub,map_mul,map_pow,map_ofNat] at h
      have hy := coordinate_mul_inverse 1
      linear_combination inverseCoordinate 1^3*h-
        (algebraMap ECProjectiveScheme.CoordinateRing (LocalizedRing 1) ECProjectiveScheme.z*
          inverseCoordinate 1*(1+algebraMap ECProjectiveScheme.CoordinateRing (LocalizedRing 1)
            ECProjectiveScheme.y*inverseCoordinate 1))*hy
    intro p hp
    exact hker hp)

@[simp] theorem infinityToChart_x : infinityToChart x=ratio 1 0 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 0)=_
  simp
@[simp] theorem infinityToChart_z : infinityToChart z=ratio 1 2 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 1)=_
  simp

theorem chartToInfinity_comp : chartToInfinity.comp infinityToChart=AlgHom.id ℚ CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity (infinityToChart x)=x
    rw [infinityToChart_x,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart z)=z
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl

theorem infinityToChart_comp : infinityToChart.comp chartToInfinity=AlgHom.id ℚ (ChartRing 1) := by
  apply chartAlgHom_ext 1
  intro i
  fin_cases i <;> simp [ratio_self]

def yChartRingEquiv : ECProjectiveScheme.yChartRing≃ₐ[ℚ]CoordinateRing :=
  {chartToInfinity with
    invFun:=infinityToChart
    left_inv:=fun q=>AlgHom.congr_fun infinityToChart_comp q
    right_inv:=fun q=>AlgHom.congr_fun chartToInfinity_comp q}

def yChartSchemeIso : ECProjectiveScheme.yOpen.toScheme≅scheme :=
  yChartIso ≪≫ Scheme.Spec.mapIso yChartRingEquiv.toRingEquiv.toCommRingCatIso.symm.op

theorem yChartSchemeIso_structureMap : yChartSchemeIso.hom≫structureMap=
    ECProjectiveScheme.yOpen.ι≫ECProjectiveScheme.structureMap := by
  apply (cancel_epi yChartIso.inv).mp
  rw [←Category.assoc,←Category.assoc]
  change (yChartIso.inv≫yChartSchemeIso.hom)≫structureMap=
    ECProjectiveScheme.chartInclusion 1≫ECProjectiveScheme.structureMap
  rw [ECProjectiveScheme.chartInclusion_structureMap,yChartSchemeIso,
    Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom yChartRingEquiv.symm.toRingHom)≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ CoordinateRing))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val (yChartRingEquiv.symm.commutes q)

end
end Z2Z4Rank6.ECProjectiveSchemeInfinity
