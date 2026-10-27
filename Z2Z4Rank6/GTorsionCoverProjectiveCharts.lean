module

public import Z2Z4Rank6.GTorsionCoverProjectiveRatios
public import Z2Z4Rank6.GTorsionCoverInfinity
public import Z2Z4Rank6.GTorsionCoverEquations

@[expose] public section

/-! Exact dehomogenization of both weighted projective charts. -/
namespace Z2Z4Rank6.GTorsionCoverProjectiveCharts
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverPolynomialData GTorsionCoverEquations
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rationalAlgHom {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→+*B) : A→ₐ[ℚ]B :=
  {toRingHom := f
   commutes' := by
    intro q
    exact RingHom.congr_fun
      (RingHom.ext_rat (f.comp (algebraMap ℚ A)) (algebraMap ℚ B)) q}

theorem map_binary_alg {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A→ₐ[ℚ]B) (ε : Bool) (z m : A) (i : Fin 2) :
    f (binary ε z m i)=binary ε (f z) (f m) i :=
  GTorsionCoverEquations.map_binary f.toRingHom ε z m i

def atZOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](GTorsionCoverAffine.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![GTorsionCoverAffine.m ε,GTorsionCoverAffine.u ε,1,GTorsionCoverAffine.r ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![GTorsionCoverAffine.m ε,GTorsionCoverAffine.u ε,1,GTorsionCoverAffine.r ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![GTorsionCoverAffine.m ε,GTorsionCoverAffine.u ε,1,GTorsionCoverAffine.r ε]) (relation ε i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (DoubleSquareCover.root (GTorsionCoverAffine.radicand ε) 0)^2-
          binary ε 1 (GTorsionCoverAffine.m ε) 0=0
        exact sub_eq_zero.mpr ((GTorsionCoverAffine.root_sq ε 0).trans (aeval_affine ε _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (DoubleSquareCover.root (GTorsionCoverAffine.radicand ε) 1)^2-
          binary ε 1 (GTorsionCoverAffine.m ε) 1=0
        exact sub_eq_zero.mpr ((GTorsionCoverAffine.root_sq ε 1).trans (aeval_affine ε _ 1))
    intro p hp
    exact hker hp)
@[simp] theorem atZOne_coordinate (ε : Bool) (i : Fin 4) :
    atZOne ε (coordinate ε i)=![GTorsionCoverAffine.m ε,GTorsionCoverAffine.u ε,1,GTorsionCoverAffine.r ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine (ε : Bool) : ChartRing ε 2→ₐ[ℚ](GTorsionCoverAffine.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atZOne ε).toRingHom (coordinate ε 2)
    (by simp)).comp (algebraMap (ChartRing ε 2) (LocalizedRing ε 2)))
@[simp] theorem chartToAffine_ratio (ε : Bool) (i : Fin 4) :
    chartToAffine ε (zRatio ε i)=![GTorsionCoverAffine.m ε,GTorsionCoverAffine.u ε,1,GTorsionCoverAffine.r ε] i := by
  change Localization.awayLift (atZOne ε).toRingHom (coordinate ε 2) (by simp)
    (zRatio ε i).val=_
  rw [ratio_val,map_mul,map_pow,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atZOne ε).toRingHom (coordinate ε 2)
      (by simp)) (inverseCoordinate ε 2)=1 := by
    have h := congrArg (Localization.awayLift (atZOne ε).toRingHom (coordinate ε 2)
      (by simp)) (coordinate_mul_inverse ε 2)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne ε (coordinate ε 2)*_ = 1 at h
    simpa using h
  rw [hi,one_pow,mul_one]
  exact atZOne_coordinate ε i

def affineToChart (ε : Bool) : (GTorsionCoverAffine.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 2) :=
  DoubleSquareCover.lift (affineRadicand ε) (zRatio ε 0)
    ![zRatio ε 1,zRatio ε 3] (by
      intro i
      rw [aeval_affine]
      fin_cases i
      · exact zRatio_u_sq ε
      · exact zRatio_r_sq ε)
@[simp] theorem affineToChart_m (ε : Bool) :
    affineToChart ε (GTorsionCoverAffine.m ε)=zRatio ε 0 := by
  simp [affineToChart, GTorsionCoverAffine.m]
@[simp] theorem affineToChart_u (ε : Bool) :
    affineToChart ε (GTorsionCoverAffine.u ε)=zRatio ε 1 := by
  simp [affineToChart, GTorsionCoverAffine.u]
@[simp] theorem affineToChart_r (ε : Bool) :
    affineToChart ε (GTorsionCoverAffine.r ε)=zRatio ε 3 := by
  simp [affineToChart, GTorsionCoverAffine.r]

theorem chartToAffine_comp (ε : Bool) :
    (chartToAffine ε).comp (affineToChart ε)=AlgHom.id ℚ (GTorsionCoverAffine.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine ε (affineToChart ε (GTorsionCoverAffine.m ε))=GTorsionCoverAffine.m ε
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (GTorsionCoverAffine.u ε))=GTorsionCoverAffine.u ε
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (GTorsionCoverAffine.r ε))=GTorsionCoverAffine.r ε
    rw [affineToChart_r,chartToAffine_ratio]
    rfl

theorem affineToChart_comp (ε : Bool) :
    (affineToChart ε).comp (chartToAffine ε)=AlgHom.id ℚ (ChartRing ε 2) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 2 rfl
  intro i
  fin_cases i <;> simp

def zChartRingEquiv (ε : Bool) : ChartRing ε 2≃ₐ[ℚ](GTorsionCoverAffine.CoordinateRing ε) :=
  {chartToAffine ε with
    invFun := affineToChart ε
    left_inv := fun x => AlgHom.congr_fun (affineToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToAffine_comp ε) x}

def zChartSchemeIso (ε : Bool) : (zOpen ε).toScheme≅GTorsionCoverAffine.scheme ε :=
  zChartIso ε ≪≫ Scheme.Spec.mapIso (zChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

def atMOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](GTorsionCoverInfinity.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![1,GTorsionCoverInfinity.U ε,GTorsionCoverInfinity.z ε,GTorsionCoverInfinity.R ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![1,GTorsionCoverInfinity.U ε,GTorsionCoverInfinity.z ε,GTorsionCoverInfinity.R ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![1,GTorsionCoverInfinity.U ε,GTorsionCoverInfinity.z ε,GTorsionCoverInfinity.R ε]) (relation ε i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (DoubleSquareCover.root (GTorsionCoverInfinity.radicand ε) 0)^2-
          binary ε (GTorsionCoverInfinity.z ε) 1 0=0
        exact sub_eq_zero.mpr ((GTorsionCoverInfinity.root_sq ε 0).trans (aeval_infinity ε _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (DoubleSquareCover.root (GTorsionCoverInfinity.radicand ε) 1)^2-
          binary ε (GTorsionCoverInfinity.z ε) 1 1=0
        exact sub_eq_zero.mpr ((GTorsionCoverInfinity.root_sq ε 1).trans (aeval_infinity ε _ 1))
    intro p hp
    exact hker hp)
@[simp] theorem atMOne_coordinate (ε : Bool) (i : Fin 4) :
    atMOne ε (coordinate ε i)=![1,GTorsionCoverInfinity.U ε,GTorsionCoverInfinity.z ε,GTorsionCoverInfinity.R ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity (ε : Bool) : ChartRing ε 0→ₐ[ℚ](GTorsionCoverInfinity.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0)
    (by simp)).comp (algebraMap (ChartRing ε 0) (LocalizedRing ε 0)))
@[simp] theorem chartToInfinity_ratio (ε : Bool) (i : Fin 4) :
    chartToInfinity ε (mRatio ε i)=![1,GTorsionCoverInfinity.U ε,GTorsionCoverInfinity.z ε,GTorsionCoverInfinity.R ε] i := by
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

def infinityToChart (ε : Bool) : (GTorsionCoverInfinity.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 0) :=
  DoubleSquareCover.lift (infinityRadicand ε) (mRatio ε 2)
    ![mRatio ε 1,mRatio ε 3] (by
      intro i
      rw [aeval_infinity]
      fin_cases i
      · exact mRatio_u_sq ε
      · exact mRatio_r_sq ε)
@[simp] theorem infinityToChart_z (ε : Bool) :
    infinityToChart ε (GTorsionCoverInfinity.z ε)=mRatio ε 2 := by
  simp [infinityToChart, GTorsionCoverInfinity.z]
@[simp] theorem infinityToChart_U (ε : Bool) :
    infinityToChart ε (GTorsionCoverInfinity.U ε)=mRatio ε 1 := by
  simp [infinityToChart, GTorsionCoverInfinity.U]
@[simp] theorem infinityToChart_R (ε : Bool) :
    infinityToChart ε (GTorsionCoverInfinity.R ε)=mRatio ε 3 := by
  simp [infinityToChart, GTorsionCoverInfinity.R]

theorem chartToInfinity_comp (ε : Bool) :
    (chartToInfinity ε).comp (infinityToChart ε)=AlgHom.id ℚ (GTorsionCoverInfinity.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity ε (infinityToChart ε (GTorsionCoverInfinity.z ε))=GTorsionCoverInfinity.z ε
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (GTorsionCoverInfinity.U ε))=GTorsionCoverInfinity.U ε
    rw [infinityToChart_U,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (GTorsionCoverInfinity.R ε))=GTorsionCoverInfinity.R ε
    rw [infinityToChart_R,chartToInfinity_ratio]
    rfl

theorem infinityToChart_comp (ε : Bool) :
    (infinityToChart ε).comp (chartToInfinity ε)=AlgHom.id ℚ (ChartRing ε 0) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 0 rfl
  intro i
  fin_cases i <;> simp

def mChartRingEquiv (ε : Bool) : ChartRing ε 0≃ₐ[ℚ](GTorsionCoverInfinity.CoordinateRing ε) :=
  {chartToInfinity ε with
    invFun := infinityToChart ε
    left_inv := fun x => AlgHom.congr_fun (infinityToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToInfinity_comp ε) x}

def mChartSchemeIso (ε : Bool) : (mOpen ε).toScheme≅GTorsionCoverInfinity.scheme ε :=
  mChartIso ε ≪≫ Scheme.Spec.mapIso (mChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

theorem zChartSchemeIso_structureMap (ε : Bool) :
    (zChartSchemeIso ε).hom ≫ GTorsionCoverAffine.structureMap ε=
      (zOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (zChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((zChartIso ε).inv ≫ (zChartSchemeIso ε).hom) ≫ GTorsionCoverAffine.structureMap ε=
    chartInclusion ε 2 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (zChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (GTorsionCoverAffine.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((zChartRingEquiv ε).symm.commutes q)

theorem mChartSchemeIso_structureMap (ε : Bool) :
    (mChartSchemeIso ε).hom ≫ GTorsionCoverInfinity.structureMap ε=
      (mOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (mChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((mChartIso ε).inv ≫ (mChartSchemeIso ε).hom) ≫ GTorsionCoverInfinity.structureMap ε=
    chartInclusion ε 0 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [mChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (mChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (GTorsionCoverInfinity.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((mChartRingEquiv ε).symm.commutes q)

end
end Z2Z4Rank6.GTorsionCoverProjectiveCharts
