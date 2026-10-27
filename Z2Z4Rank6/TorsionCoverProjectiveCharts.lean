module

public import Z2Z4Rank6.TorsionCoverProjectiveRatios
public import Z2Z4Rank6.TorsionCoverInfinity

@[expose] public section

/-! Exact dehomogenization of both weighted projective charts. -/
namespace Z2Z4Rank6.TorsionCoverProjectiveCharts
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
open TorsionCoverProjective TorsionCoverPolynomialData
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rationalAlgHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→+*B) : A→ₐ[ℚ]B :=
  {toRingHom := f
   commutes' := by
    intro q
    exact RingHom.congr_fun
      (RingHom.ext_rat (f.comp (algebraMap ℚ A)) (algebraMap ℚ B)) q}

def atZOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](TorsionCoverAffine.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![TorsionCoverAffine.m ε,TorsionCoverAffine.u ε,TorsionCoverAffine.v ε,1,TorsionCoverAffine.r ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![TorsionCoverAffine.m ε,TorsionCoverAffine.u ε,TorsionCoverAffine.v ε,1,TorsionCoverAffine.r ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![TorsionCoverAffine.m ε,TorsionCoverAffine.u ε,TorsionCoverAffine.v ε,1,TorsionCoverAffine.r ε]) (relation ε i)=0
      fin_cases i
      · have h := TorsionCoverAffine.root_sq ε 0
        norm_num [TorsionCoverAffine.radicand,affineRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        linear_combination h
      · have h := TorsionCoverAffine.root_sq ε 1
        norm_num [TorsionCoverAffine.radicand,affineRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        linear_combination h
      · have h := TorsionCoverAffine.root_sq ε 2
        norm_num [TorsionCoverAffine.radicand,affineRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        linear_combination h
    intro p hp
    exact hker hp)
@[simp] theorem atZOne_coordinate (ε : Bool) (i : Fin 5) :
    atZOne ε (coordinate ε i)=![TorsionCoverAffine.m ε,TorsionCoverAffine.u ε,TorsionCoverAffine.v ε,1,TorsionCoverAffine.r ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine (ε : Bool) : ChartRing ε 3→ₐ[ℚ](TorsionCoverAffine.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atZOne ε).toRingHom (coordinate ε 3)
    (by simp)).comp (algebraMap (ChartRing ε 3) (LocalizedRing ε 3)))
@[simp] theorem chartToAffine_ratio (ε : Bool) (i : Fin 5) :
    chartToAffine ε (zRatio ε i)=![TorsionCoverAffine.m ε,TorsionCoverAffine.u ε,TorsionCoverAffine.v ε,1,TorsionCoverAffine.r ε] i := by
  change Localization.awayLift (atZOne ε).toRingHom (coordinate ε 3) (by simp)
    (zRatio ε i).val=_
  rw [ratio_val,map_mul,map_pow,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atZOne ε).toRingHom (coordinate ε 3)
      (by simp)) (inverseCoordinate ε 3)=1 := by
    have h := congrArg (Localization.awayLift (atZOne ε).toRingHom (coordinate ε 3)
      (by simp)) (coordinate_mul_inverse ε 3)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne ε (coordinate ε 3)*_ = 1 at h
    simpa using h
  rw [hi,one_pow,mul_one]
  exact atZOne_coordinate ε i

def affineToChart (ε : Bool) : (TorsionCoverAffine.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 3) :=
  TripleSquareCover.lift (affineRadicand ε) (zRatio ε 0)
    ![zRatio ε 1,zRatio ε 2,zRatio ε 4] (by
      intro i
      fin_cases i
      · norm_num [affineRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        simpa [a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] using zRatio_u_sq ε
      · norm_num [affineRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        simpa [a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] using zRatio_v_sq ε
      · norm_num [affineRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        have h := zRatio_r_sq ε
        dsimp [a,b] at h
        linear_combination h)
@[simp] theorem affineToChart_m (ε : Bool) :
    affineToChart ε (TorsionCoverAffine.m ε)=zRatio ε 0 := by
  simp [affineToChart, TorsionCoverAffine.m]
@[simp] theorem affineToChart_u (ε : Bool) :
    affineToChart ε (TorsionCoverAffine.u ε)=zRatio ε 1 := by
  simp [affineToChart, TorsionCoverAffine.u]
@[simp] theorem affineToChart_v (ε : Bool) :
    affineToChart ε (TorsionCoverAffine.v ε)=zRatio ε 2 := by
  simp [affineToChart, TorsionCoverAffine.v]
@[simp] theorem affineToChart_r (ε : Bool) :
    affineToChart ε (TorsionCoverAffine.r ε)=zRatio ε 4 := by
  simp [affineToChart, TorsionCoverAffine.r]

theorem chartToAffine_comp (ε : Bool) :
    (chartToAffine ε).comp (affineToChart ε)=AlgHom.id ℚ (TorsionCoverAffine.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine ε (affineToChart ε (TorsionCoverAffine.m ε))=TorsionCoverAffine.m ε
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (TorsionCoverAffine.u ε))=TorsionCoverAffine.u ε
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (TorsionCoverAffine.v ε))=TorsionCoverAffine.v ε
    rw [affineToChart_v,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (TorsionCoverAffine.r ε))=TorsionCoverAffine.r ε
    rw [affineToChart_r,chartToAffine_ratio]
    rfl

theorem affineToChart_comp (ε : Bool) :
    (affineToChart ε).comp (chartToAffine ε)=AlgHom.id ℚ (ChartRing ε 3) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 3 rfl
  intro i
  fin_cases i <;> simp

def zChartRingEquiv (ε : Bool) : ChartRing ε 3≃ₐ[ℚ](TorsionCoverAffine.CoordinateRing ε) :=
  {chartToAffine ε with
    invFun := affineToChart ε
    left_inv := fun x => AlgHom.congr_fun (affineToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToAffine_comp ε) x}

def zChartSchemeIso (ε : Bool) : (zOpen ε).toScheme≅TorsionCoverAffine.scheme ε :=
  zChartIso ε ≪≫ Scheme.Spec.mapIso (zChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

def atMOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](TorsionCoverInfinity.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![1,TorsionCoverInfinity.U ε,TorsionCoverInfinity.V ε,TorsionCoverInfinity.z ε,TorsionCoverInfinity.R ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![1,TorsionCoverInfinity.U ε,TorsionCoverInfinity.V ε,TorsionCoverInfinity.z ε,TorsionCoverInfinity.R ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![1,TorsionCoverInfinity.U ε,TorsionCoverInfinity.V ε,TorsionCoverInfinity.z ε,TorsionCoverInfinity.R ε]) (relation ε i)=0
      fin_cases i
      · have h := TorsionCoverInfinity.root_sq ε 0
        norm_num [TorsionCoverInfinity.radicand,infinityRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        linear_combination h
      · have h := TorsionCoverInfinity.root_sq ε 1
        norm_num [TorsionCoverInfinity.radicand,infinityRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        linear_combination h
      · have h := TorsionCoverInfinity.root_sq ε 2
        norm_num [TorsionCoverInfinity.radicand,infinityRadicand,a,b,HeightInvariantForms.binaryA,
          HeightInvariantForms.binaryB] at h
        norm_num only [map_ofNat] at h
        norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        linear_combination h
    intro p hp
    exact hker hp)
@[simp] theorem atMOne_coordinate (ε : Bool) (i : Fin 5) :
    atMOne ε (coordinate ε i)=![1,TorsionCoverInfinity.U ε,TorsionCoverInfinity.V ε,TorsionCoverInfinity.z ε,TorsionCoverInfinity.R ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity (ε : Bool) : ChartRing ε 0→ₐ[ℚ](TorsionCoverInfinity.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0)
    (by simp)).comp (algebraMap (ChartRing ε 0) (LocalizedRing ε 0)))
@[simp] theorem chartToInfinity_ratio (ε : Bool) (i : Fin 5) :
    chartToInfinity ε (mRatio ε i)=![1,TorsionCoverInfinity.U ε,TorsionCoverInfinity.V ε,TorsionCoverInfinity.z ε,TorsionCoverInfinity.R ε] i := by
  change Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0) (by simp)
    (mRatio ε i).val=_
  rw [ratio_val,map_mul,map_pow,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0)
      (by simp)) (inverseCoordinate ε 0)=1 := by
    have h := congrArg (Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0)
      (by simp)) (coordinate_mul_inverse ε 0)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atMOne ε (coordinate ε 0)*_ = 1 at h
    simpa using h
  rw [hi,one_pow,mul_one]
  exact atMOne_coordinate ε i

def infinityToChart (ε : Bool) : (TorsionCoverInfinity.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 0) :=
  TripleSquareCover.lift (infinityRadicand ε) (mRatio ε 3)
    ![mRatio ε 1,mRatio ε 2,mRatio ε 4] (by
      intro i
      fin_cases i
      · norm_num [infinityRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        simpa [a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] using mRatio_u_sq ε
      · norm_num [infinityRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        simpa [a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] using mRatio_v_sq ε
      · norm_num [infinityRadicand,a,b,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
        norm_num only [map_ofNat]
        have h := mRatio_r_sq ε
        dsimp [HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] at h
        linear_combination h)
@[simp] theorem infinityToChart_z (ε : Bool) :
    infinityToChart ε (TorsionCoverInfinity.z ε)=mRatio ε 3 := by
  simp [infinityToChart, TorsionCoverInfinity.z]
@[simp] theorem infinityToChart_U (ε : Bool) :
    infinityToChart ε (TorsionCoverInfinity.U ε)=mRatio ε 1 := by
  simp [infinityToChart, TorsionCoverInfinity.U]
@[simp] theorem infinityToChart_V (ε : Bool) :
    infinityToChart ε (TorsionCoverInfinity.V ε)=mRatio ε 2 := by
  simp [infinityToChart, TorsionCoverInfinity.V]
@[simp] theorem infinityToChart_R (ε : Bool) :
    infinityToChart ε (TorsionCoverInfinity.R ε)=mRatio ε 4 := by
  simp [infinityToChart, TorsionCoverInfinity.R]

theorem chartToInfinity_comp (ε : Bool) :
    (chartToInfinity ε).comp (infinityToChart ε)=AlgHom.id ℚ (TorsionCoverInfinity.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity ε (infinityToChart ε (TorsionCoverInfinity.z ε))=TorsionCoverInfinity.z ε
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (TorsionCoverInfinity.U ε))=TorsionCoverInfinity.U ε
    rw [infinityToChart_U,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (TorsionCoverInfinity.V ε))=TorsionCoverInfinity.V ε
    rw [infinityToChart_V,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (TorsionCoverInfinity.R ε))=TorsionCoverInfinity.R ε
    rw [infinityToChart_R,chartToInfinity_ratio]
    rfl

theorem infinityToChart_comp (ε : Bool) :
    (infinityToChart ε).comp (chartToInfinity ε)=AlgHom.id ℚ (ChartRing ε 0) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 0 rfl
  intro i
  fin_cases i <;> simp

def mChartRingEquiv (ε : Bool) : ChartRing ε 0≃ₐ[ℚ](TorsionCoverInfinity.CoordinateRing ε) :=
  {chartToInfinity ε with
    invFun := infinityToChart ε
    left_inv := fun x => AlgHom.congr_fun (infinityToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToInfinity_comp ε) x}

def mChartSchemeIso (ε : Bool) : (mOpen ε).toScheme≅TorsionCoverInfinity.scheme ε :=
  mChartIso ε ≪≫ Scheme.Spec.mapIso (mChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

theorem zChartSchemeIso_structureMap (ε : Bool) :
    (zChartSchemeIso ε).hom ≫ TorsionCoverAffine.structureMap ε=
      (zOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (zChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((zChartIso ε).inv ≫ (zChartSchemeIso ε).hom) ≫ TorsionCoverAffine.structureMap ε=
    chartInclusion ε 3 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (zChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (TorsionCoverAffine.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((zChartRingEquiv ε).symm.commutes q)

theorem mChartSchemeIso_structureMap (ε : Bool) :
    (mChartSchemeIso ε).hom ≫ TorsionCoverInfinity.structureMap ε=
      (mOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (mChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((mChartIso ε).inv ≫ (mChartSchemeIso ε).hom) ≫ TorsionCoverInfinity.structureMap ε=
    chartInclusion ε 0 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [mChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (mChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (TorsionCoverInfinity.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((mChartRingEquiv ε).symm.commutes q)

end
end Z2Z4Rank6.TorsionCoverProjectiveCharts
