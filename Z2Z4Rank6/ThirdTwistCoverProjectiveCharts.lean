import Z2Z4Rank6.ThirdTwistCoverProjectiveRatios
import Z2Z4Rank6.ThirdTwistCoverInfinity
import Z2Z4Rank6.ThirdTwistCoverEquations

/-! Exact dehomogenization of both weighted projective charts. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverPolynomialData ThirdTwistCoverEquations
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
    (f : A→ₐ[ℚ]B)  (z m : A) (i : Fin 3) :
    f (binary z m i)=binary (f z) (f m) i :=
  ThirdTwistCoverEquations.map_binary f.toRingHom z m i

def atZOne  : CoordinateRing→ₐ[ℚ](ThirdTwistCoverAffine.CoordinateRing) :=
  Ideal.Quotient.liftₐ (definingIdeal) (MvPolynomial.aeval ![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r]) (relation i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) 0)^2-
          binary 1 (ThirdTwistCoverAffine.m) 0=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverAffine.root_sq 0).trans (aeval_affine _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) 1)^2-
          binary 1 (ThirdTwistCoverAffine.m) 1=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverAffine.root_sq 1).trans (aeval_affine _ 1))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) 2)^2-
          binary 1 (ThirdTwistCoverAffine.m) 2=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverAffine.root_sq 2).trans (aeval_affine _ 2))
    intro p hp
    exact hker hp)
@[simp] theorem atZOne_coordinate  (i : Fin 5) :
    atZOne (coordinate i)=![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine  : ChartRing 3→ₐ[ℚ](ThirdTwistCoverAffine.CoordinateRing) :=
  rationalAlgHom ((Localization.awayLift (atZOne).toRingHom (coordinate 3)
    (by simp)).comp (algebraMap (ChartRing 3) (LocalizedRing 3)))
@[simp] theorem chartToAffine_ratio  (i : Fin 5) :
    chartToAffine (zRatio i)=![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r] i := by
  change Localization.awayLift (atZOne).toRingHom (coordinate 3) (by simp)
    (zRatio i).val=_
  rw [ratio_val,map_mul,map_pow,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atZOne).toRingHom (coordinate 3)
      (by simp)) (inverseCoordinate 3)=1 := by
    have h := congrArg (Localization.awayLift (atZOne).toRingHom (coordinate 3)
      (by simp)) (coordinate_mul_inverse 3)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne (coordinate 3)*_ = 1 at h
    simpa using h
  rw [hi,one_pow,mul_one]
  exact atZOne_coordinate i

def affineToChart  : (ThirdTwistCoverAffine.CoordinateRing)→ₐ[ℚ](ChartRing 3) :=
  TripleSquareCover.lift (affineRadicand) (zRatio 0)
    ![zRatio 1,zRatio 2,zRatio 4] (by
      intro i
      rw [aeval_affine]
      fin_cases i
      · exact zRatio_u_sq
      · exact zRatio_v_sq
      · exact zRatio_r_sq)
@[simp] theorem affineToChart_m  :
    affineToChart (ThirdTwistCoverAffine.m)=zRatio 0 := by
  simp [affineToChart, ThirdTwistCoverAffine.m]
@[simp] theorem affineToChart_u  :
    affineToChart (ThirdTwistCoverAffine.u)=zRatio 1 := by
  simp [affineToChart, ThirdTwistCoverAffine.u]
@[simp] theorem affineToChart_v  :
    affineToChart (ThirdTwistCoverAffine.v)=zRatio 2 := by
  simp [affineToChart, ThirdTwistCoverAffine.v]
@[simp] theorem affineToChart_r  :
    affineToChart (ThirdTwistCoverAffine.r)=zRatio 4 := by
  simp [affineToChart, ThirdTwistCoverAffine.r]

theorem chartToAffine_comp  :
    (chartToAffine).comp (affineToChart)=AlgHom.id ℚ (ThirdTwistCoverAffine.CoordinateRing) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine (affineToChart (ThirdTwistCoverAffine.m))=ThirdTwistCoverAffine.m
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart (ThirdTwistCoverAffine.u))=ThirdTwistCoverAffine.u
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart (ThirdTwistCoverAffine.v))=ThirdTwistCoverAffine.v
    rw [affineToChart_v,chartToAffine_ratio]
    rfl
  · change chartToAffine (affineToChart (ThirdTwistCoverAffine.r))=ThirdTwistCoverAffine.r
    rw [affineToChart_r,chartToAffine_ratio]
    rfl

theorem affineToChart_comp  :
    (affineToChart).comp (chartToAffine)=AlgHom.id ℚ (ChartRing 3) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext 3 rfl
  intro i
  fin_cases i <;> simp

def zChartRingEquiv  : ChartRing 3≃ₐ[ℚ](ThirdTwistCoverAffine.CoordinateRing) :=
  {chartToAffine with
    invFun := affineToChart
    left_inv := fun x => AlgHom.congr_fun (affineToChart_comp) x
    right_inv := fun x => AlgHom.congr_fun (chartToAffine_comp) x}

def zChartSchemeIso  : (zOpen).toScheme≅ThirdTwistCoverAffine.scheme :=
  zChartIso ≪≫ Scheme.Spec.mapIso (zChartRingEquiv).toRingEquiv.toCommRingCatIso.symm.op

def atMOne  : CoordinateRing→ₐ[ℚ](ThirdTwistCoverInfinity.CoordinateRing) :=
  Ideal.Quotient.liftₐ (definingIdeal) (MvPolynomial.aeval ![1,ThirdTwistCoverInfinity.U,ThirdTwistCoverInfinity.V,ThirdTwistCoverInfinity.z,ThirdTwistCoverInfinity.R]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![1,ThirdTwistCoverInfinity.U,ThirdTwistCoverInfinity.V,ThirdTwistCoverInfinity.z,ThirdTwistCoverInfinity.R]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![1,ThirdTwistCoverInfinity.U,ThirdTwistCoverInfinity.V,ThirdTwistCoverInfinity.z,ThirdTwistCoverInfinity.R]) (relation i)=0
      fin_cases i
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverInfinity.radicand) 0)^2-
          binary (ThirdTwistCoverInfinity.z) 1 0=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverInfinity.root_sq 0).trans (aeval_infinity _ 0))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverInfinity.radicand) 1)^2-
          binary (ThirdTwistCoverInfinity.z) 1 1=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverInfinity.root_sq 1).trans (aeval_infinity _ 1))
      · rw [relation,map_sub,map_pow,map_binary_alg]
        simp only [MvPolynomial.aeval_X]
        change (TripleSquareCover.root (ThirdTwistCoverInfinity.radicand) 2)^2-
          binary (ThirdTwistCoverInfinity.z) 1 2=0
        exact sub_eq_zero.mpr ((ThirdTwistCoverInfinity.root_sq 2).trans (aeval_infinity _ 2))
    intro p hp
    exact hker hp)
@[simp] theorem atMOne_coordinate  (i : Fin 5) :
    atMOne (coordinate i)=![1,ThirdTwistCoverInfinity.U,ThirdTwistCoverInfinity.V,ThirdTwistCoverInfinity.z,ThirdTwistCoverInfinity.R] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity  : ChartRing 0→ₐ[ℚ](ThirdTwistCoverInfinity.CoordinateRing) :=
  rationalAlgHom ((Localization.awayLift (atMOne).toRingHom (coordinate 0)
    (by simp)).comp (algebraMap (ChartRing 0) (LocalizedRing 0)))
@[simp] theorem chartToInfinity_ratio  (i : Fin 5) :
    chartToInfinity (mRatio i)=![1,ThirdTwistCoverInfinity.U,ThirdTwistCoverInfinity.V,ThirdTwistCoverInfinity.z,ThirdTwistCoverInfinity.R] i := by
  change Localization.awayLift (atMOne).toRingHom (coordinate 0) (by simp)
    (mRatio i).val=_
  rw [ratio_val,map_mul,map_pow,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atMOne).toRingHom (coordinate 0)
      (by simp)) (inverseCoordinate 0)=1 := by
    have h := congrArg (Localization.awayLift (atMOne).toRingHom (coordinate 0)
      (by simp)) (coordinate_mul_inverse 0)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atMOne (coordinate 0)*_ = 1 at h
    simpa using h
  rw [hi,one_pow,mul_one]
  exact atMOne_coordinate i

def infinityToChart  : (ThirdTwistCoverInfinity.CoordinateRing)→ₐ[ℚ](ChartRing 0) :=
  TripleSquareCover.lift (infinityRadicand) (mRatio 3)
    ![mRatio 1,mRatio 2,mRatio 4] (by
      intro i
      rw [aeval_infinity]
      fin_cases i
      · exact mRatio_u_sq
      · exact mRatio_v_sq
      · exact mRatio_r_sq)
@[simp] theorem infinityToChart_z  :
    infinityToChart (ThirdTwistCoverInfinity.z)=mRatio 3 := by
  simp [infinityToChart, ThirdTwistCoverInfinity.z]
@[simp] theorem infinityToChart_U  :
    infinityToChart (ThirdTwistCoverInfinity.U)=mRatio 1 := by
  simp [infinityToChart, ThirdTwistCoverInfinity.U]
@[simp] theorem infinityToChart_V  :
    infinityToChart (ThirdTwistCoverInfinity.V)=mRatio 2 := by
  simp [infinityToChart, ThirdTwistCoverInfinity.V]
@[simp] theorem infinityToChart_R  :
    infinityToChart (ThirdTwistCoverInfinity.R)=mRatio 4 := by
  simp [infinityToChart, ThirdTwistCoverInfinity.R]

theorem chartToInfinity_comp  :
    (chartToInfinity).comp (infinityToChart)=AlgHom.id ℚ (ThirdTwistCoverInfinity.CoordinateRing) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity (infinityToChart (ThirdTwistCoverInfinity.z))=ThirdTwistCoverInfinity.z
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart (ThirdTwistCoverInfinity.U))=ThirdTwistCoverInfinity.U
    rw [infinityToChart_U,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart (ThirdTwistCoverInfinity.V))=ThirdTwistCoverInfinity.V
    rw [infinityToChart_V,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart (ThirdTwistCoverInfinity.R))=ThirdTwistCoverInfinity.R
    rw [infinityToChart_R,chartToInfinity_ratio]
    rfl

theorem infinityToChart_comp  :
    (infinityToChart).comp (chartToInfinity)=AlgHom.id ℚ (ChartRing 0) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext 0 rfl
  intro i
  fin_cases i <;> simp

def mChartRingEquiv  : ChartRing 0≃ₐ[ℚ](ThirdTwistCoverInfinity.CoordinateRing) :=
  {chartToInfinity with
    invFun := infinityToChart
    left_inv := fun x => AlgHom.congr_fun (infinityToChart_comp) x
    right_inv := fun x => AlgHom.congr_fun (chartToInfinity_comp) x}

def mChartSchemeIso  : (mOpen).toScheme≅ThirdTwistCoverInfinity.scheme :=
  mChartIso ≪≫ Scheme.Spec.mapIso (mChartRingEquiv).toRingEquiv.toCommRingCatIso.symm.op

theorem zChartSchemeIso_structureMap  :
    (zChartSchemeIso).hom ≫ ThirdTwistCoverAffine.structureMap=
      (zOpen).ι ≫ structureMap := by
  apply (cancel_epi (zChartIso).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((zChartIso).inv ≫ (zChartSchemeIso).hom) ≫ ThirdTwistCoverAffine.structureMap=
    chartInclusion 3 ≫ structureMap
  rw [chartInclusion_structureMap]
  rw [zChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (zChartRingEquiv).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (ThirdTwistCoverAffine.CoordinateRing)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((zChartRingEquiv).symm.commutes q)

theorem mChartSchemeIso_structureMap  :
    (mChartSchemeIso).hom ≫ ThirdTwistCoverInfinity.structureMap=
      (mOpen).ι ≫ structureMap := by
  apply (cancel_epi (mChartIso).inv).mp
  rw [←Category.assoc,←Category.assoc]
  change ((mChartIso).inv ≫ (mChartSchemeIso).hom) ≫ ThirdTwistCoverInfinity.structureMap=
    chartInclusion 0 ≫ structureMap
  rw [chartInclusion_structureMap]
  rw [mChartSchemeIso,Iso.trans_hom,Iso.inv_hom_id_assoc]
  change Spec.map (CommRingCat.ofHom (mChartRingEquiv).symm.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (ThirdTwistCoverInfinity.CoordinateRing)))=_
  rw [←Spec.map_comp]
  congr 1
  ext q
  exact congrArg HomogeneousLocalization.val ((mChartRingEquiv).symm.commutes q)

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
