import Z2Z4Rank6.SecondTorsionCoverProjectiveRatios
import Z2Z4Rank6.SecondTorsionCoverInfinity
import Z2Z4Rank6.SecondTorsionCoverEquations

/-! Exact dehomogenization of both weighted projective charts. -/
namespace Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
open SecondTorsionCoverProjective SecondTorsionCoverPolynomialData SecondTorsionCoverEquations
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
    (f : A→ₐ[ℚ]B) (ε : Bool) (z m : A) (i : Fin 3) :
    f (binary ε z m i)=binary ε (f z) (f m) i :=
  SecondTorsionCoverEquations.map_binary f.toRingHom ε z m i

def atZOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](SecondTorsionCoverAffine.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε]) (relation ε i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverAffine.radicand ε) 0)^2-
          binary ε 1 (SecondTorsionCoverAffine.m ε) 0=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverAffine.root_sq ε 0).trans (aeval_affine ε _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverAffine.radicand ε) 1)^2-
          binary ε 1 (SecondTorsionCoverAffine.m ε) 1=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverAffine.root_sq ε 1).trans (aeval_affine ε _ 1))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverAffine.radicand ε) 2)^2-
          binary ε 1 (SecondTorsionCoverAffine.m ε) 2=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverAffine.root_sq ε 2).trans (aeval_affine ε _ 2))
    intro p hp
    exact hker hp)
@[simp] theorem atZOne_coordinate (ε : Bool) (i : Fin 5) :
    atZOne ε (coordinate ε i)=![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine (ε : Bool) : ChartRing ε 3→ₐ[ℚ](SecondTorsionCoverAffine.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atZOne ε).toRingHom (coordinate ε 3)
    (by simp)).comp (algebraMap (ChartRing ε 3) (LocalizedRing ε 3)))
@[simp] theorem chartToAffine_ratio (ε : Bool) (i : Fin 5) :
    chartToAffine ε (zRatio ε i)=![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε] i := by
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

def affineToChart (ε : Bool) : (SecondTorsionCoverAffine.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 3) :=
  TripleSquareCover.lift (affineRadicand ε) (zRatio ε 0)
    ![zRatio ε 1,zRatio ε 2,zRatio ε 4] (by
      intro i
      rw [aeval_affine]
      fin_cases i
      · exact zRatio_u_sq ε
      · exact zRatio_v_sq ε
      · exact zRatio_r_sq ε)
@[simp] theorem affineToChart_m (ε : Bool) :
    affineToChart ε (SecondTorsionCoverAffine.m ε)=zRatio ε 0 := by
  simp [affineToChart, SecondTorsionCoverAffine.m]
@[simp] theorem affineToChart_u (ε : Bool) :
    affineToChart ε (SecondTorsionCoverAffine.u ε)=zRatio ε 1 := by
  simp [affineToChart, SecondTorsionCoverAffine.u]
@[simp] theorem affineToChart_v (ε : Bool) :
    affineToChart ε (SecondTorsionCoverAffine.v ε)=zRatio ε 2 := by
  simp [affineToChart, SecondTorsionCoverAffine.v]
@[simp] theorem affineToChart_r (ε : Bool) :
    affineToChart ε (SecondTorsionCoverAffine.r ε)=zRatio ε 4 := by
  simp [affineToChart, SecondTorsionCoverAffine.r]

theorem chartToAffine_comp (ε : Bool) :
    (chartToAffine ε).comp (affineToChart ε)=AlgHom.id ℚ (SecondTorsionCoverAffine.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine ε (affineToChart ε (SecondTorsionCoverAffine.m ε))=SecondTorsionCoverAffine.m ε
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (SecondTorsionCoverAffine.u ε))=SecondTorsionCoverAffine.u ε
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (SecondTorsionCoverAffine.v ε))=SecondTorsionCoverAffine.v ε
    rw [affineToChart_v,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (SecondTorsionCoverAffine.r ε))=SecondTorsionCoverAffine.r ε
    rw [affineToChart_r,chartToAffine_ratio]
    rfl

theorem affineToChart_comp (ε : Bool) :
    (affineToChart ε).comp (chartToAffine ε)=AlgHom.id ℚ (ChartRing ε 3) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 3 rfl
  intro i
  fin_cases i <;> simp

def zChartRingEquiv (ε : Bool) : ChartRing ε 3≃ₐ[ℚ](SecondTorsionCoverAffine.CoordinateRing ε) :=
  {chartToAffine ε with
    invFun := affineToChart ε
    left_inv := fun x => AlgHom.congr_fun (affineToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToAffine_comp ε) x}

def zChartSchemeIso (ε : Bool) : (zOpen ε).toScheme≅SecondTorsionCoverAffine.scheme ε :=
  zChartIso ε ≪≫ Scheme.Spec.mapIso (zChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

def atMOne (ε : Bool) : CoordinateRing ε→ₐ[ℚ](SecondTorsionCoverInfinity.CoordinateRing ε) :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![1,SecondTorsionCoverInfinity.U ε,SecondTorsionCoverInfinity.V ε,SecondTorsionCoverInfinity.z ε,SecondTorsionCoverInfinity.R ε]) (by
    have hker : definingIdeal ε≤RingHom.ker (MvPolynomial.aeval ![1,SecondTorsionCoverInfinity.U ε,SecondTorsionCoverInfinity.V ε,SecondTorsionCoverInfinity.z ε,SecondTorsionCoverInfinity.R ε]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![1,SecondTorsionCoverInfinity.U ε,SecondTorsionCoverInfinity.V ε,SecondTorsionCoverInfinity.z ε,SecondTorsionCoverInfinity.R ε]) (relation ε i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverInfinity.radicand ε) 0)^2-
          binary ε (SecondTorsionCoverInfinity.z ε) 1 0=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverInfinity.root_sq ε 0).trans (aeval_infinity ε _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverInfinity.radicand ε) 1)^2-
          binary ε (SecondTorsionCoverInfinity.z ε) 1 1=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverInfinity.root_sq ε 1).trans (aeval_infinity ε _ 1))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (SecondTorsionCoverInfinity.radicand ε) 2)^2-
          binary ε (SecondTorsionCoverInfinity.z ε) 1 2=0
        exact sub_eq_zero.mpr ((SecondTorsionCoverInfinity.root_sq ε 2).trans (aeval_infinity ε _ 2))
    intro p hp
    exact hker hp)
@[simp] theorem atMOne_coordinate (ε : Bool) (i : Fin 5) :
    atMOne ε (coordinate ε i)=![1,SecondTorsionCoverInfinity.U ε,SecondTorsionCoverInfinity.V ε,SecondTorsionCoverInfinity.z ε,SecondTorsionCoverInfinity.R ε] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity (ε : Bool) : ChartRing ε 0→ₐ[ℚ](SecondTorsionCoverInfinity.CoordinateRing ε) :=
  rationalAlgHom ((Localization.awayLift (atMOne ε).toRingHom (coordinate ε 0)
    (by simp)).comp (algebraMap (ChartRing ε 0) (LocalizedRing ε 0)))
@[simp] theorem chartToInfinity_ratio (ε : Bool) (i : Fin 5) :
    chartToInfinity ε (mRatio ε i)=![1,SecondTorsionCoverInfinity.U ε,SecondTorsionCoverInfinity.V ε,SecondTorsionCoverInfinity.z ε,SecondTorsionCoverInfinity.R ε] i := by
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

def infinityToChart (ε : Bool) : (SecondTorsionCoverInfinity.CoordinateRing ε)→ₐ[ℚ](ChartRing ε 0) :=
  TripleSquareCover.lift (infinityRadicand ε) (mRatio ε 3)
    ![mRatio ε 1,mRatio ε 2,mRatio ε 4] (by
      intro i
      rw [aeval_infinity]
      fin_cases i
      · exact mRatio_u_sq ε
      · exact mRatio_v_sq ε
      · exact mRatio_r_sq ε)
@[simp] theorem infinityToChart_z (ε : Bool) :
    infinityToChart ε (SecondTorsionCoverInfinity.z ε)=mRatio ε 3 := by
  simp [infinityToChart, SecondTorsionCoverInfinity.z]
@[simp] theorem infinityToChart_U (ε : Bool) :
    infinityToChart ε (SecondTorsionCoverInfinity.U ε)=mRatio ε 1 := by
  simp [infinityToChart, SecondTorsionCoverInfinity.U]
@[simp] theorem infinityToChart_V (ε : Bool) :
    infinityToChart ε (SecondTorsionCoverInfinity.V ε)=mRatio ε 2 := by
  simp [infinityToChart, SecondTorsionCoverInfinity.V]
@[simp] theorem infinityToChart_R (ε : Bool) :
    infinityToChart ε (SecondTorsionCoverInfinity.R ε)=mRatio ε 4 := by
  simp [infinityToChart, SecondTorsionCoverInfinity.R]

theorem chartToInfinity_comp (ε : Bool) :
    (chartToInfinity ε).comp (infinityToChart ε)=AlgHom.id ℚ (SecondTorsionCoverInfinity.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity ε (infinityToChart ε (SecondTorsionCoverInfinity.z ε))=SecondTorsionCoverInfinity.z ε
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (SecondTorsionCoverInfinity.U ε))=SecondTorsionCoverInfinity.U ε
    rw [infinityToChart_U,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (SecondTorsionCoverInfinity.V ε))=SecondTorsionCoverInfinity.V ε
    rw [infinityToChart_V,chartToInfinity_ratio]
    rfl
  · change chartToInfinity ε (infinityToChart ε (SecondTorsionCoverInfinity.R ε))=SecondTorsionCoverInfinity.R ε
    rw [infinityToChart_R,chartToInfinity_ratio]
    rfl

theorem infinityToChart_comp (ε : Bool) :
    (infinityToChart ε).comp (chartToInfinity ε)=AlgHom.id ℚ (ChartRing ε 0) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε 0 rfl
  intro i
  fin_cases i <;> simp

def mChartRingEquiv (ε : Bool) : ChartRing ε 0≃ₐ[ℚ](SecondTorsionCoverInfinity.CoordinateRing ε) :=
  {chartToInfinity ε with
    invFun := infinityToChart ε
    left_inv := fun x => AlgHom.congr_fun (infinityToChart_comp ε) x
    right_inv := fun x => AlgHom.congr_fun (chartToInfinity_comp ε) x}

def mChartSchemeIso (ε : Bool) : (mOpen ε).toScheme≅SecondTorsionCoverInfinity.scheme ε :=
  mChartIso ε ≪≫ Scheme.Spec.mapIso (mChartRingEquiv ε).toRingEquiv.toCommRingCatIso.symm.op

theorem zChartSchemeIso_structureMap (ε : Bool) :
    (zChartSchemeIso ε).hom ≫ SecondTorsionCoverAffine.structureMap ε=
      (zOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (zChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((zChartIso ε).inv ≫ (zChartSchemeIso ε).hom) ≫ SecondTorsionCoverAffine.structureMap ε=
    chartInclusion ε 3 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (zChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (SecondTorsionCoverAffine.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((zChartRingEquiv ε).symm.commutes q)

theorem mChartSchemeIso_structureMap (ε : Bool) :
    (mChartSchemeIso ε).hom ≫ SecondTorsionCoverInfinity.structureMap ε=
      (mOpen ε).ι ≫ structureMap ε := by
  apply (cancel_epi (mChartIso ε).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((mChartIso ε).inv ≫ (mChartSchemeIso ε).hom) ≫ SecondTorsionCoverInfinity.structureMap ε=
    chartInclusion ε 0 ≫ structureMap ε
  rw [chartInclusion_structureMap]
  rw [mChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (mChartRingEquiv ε).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (SecondTorsionCoverInfinity.CoordinateRing ε)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((mChartRingEquiv ε).symm.commutes q)

end
end Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
