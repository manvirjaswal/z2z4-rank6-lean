import Z2Z4Rank6.ProjectiveBaseSchemeCharts
import Z2Z4Rank6.ProjectiveBaseSchemeInfinityData

/-!
# The affine chart at infinity

Jaswal, DOI 10.5281/zenodo.23437117, Section 3. The m≠0 chart is
identified with the quotient u²=1210z²+15, v²=1215z²+10.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeCharts
noncomputable section
open scoped Classical BigOperators
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme

/-- The quotient map setting m=1. -/
def atMOne : CoordinateRing →ₐ[ℚ] InfinityCoordinateRing :=
  Ideal.Quotient.liftₐ definingIdeal
    (MvPolynomial.aeval ![1,infinityU,infinityV,infinityZ]) (by
      have hker : definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![1,infinityU,infinityV,infinityZ]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (relation i)=0
        fin_cases i
        · norm_num [ProjectiveBaseScheme.relation]
          norm_num only [map_ofNat]
          linear_combination infinity_u_sq
        · norm_num [ProjectiveBaseScheme.relation]
          norm_num only [map_ofNat]
          linear_combination infinity_v_sq
      intro p hp
      exact hker hp)

@[simp] theorem atMOne_coordinate (i : Fin 4) :
    atMOne (coordinate i)=![1,infinityU,infinityV,infinityZ] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToInfinity : ChartRing 0 →ₐ[ℚ] InfinityCoordinateRing :=
  rationalAlgHom ((Localization.awayLift atMOne.toRingHom m (by simp [m])).comp
    (algebraMap (ChartRing 0) (LocalizedRing 0)))

@[simp] theorem chartToInfinity_ratio (i : Fin 4) :
    chartToInfinity (ratio 0 i)=![1,infinityU,infinityV,infinityZ] i := by
  change Localization.awayLift atMOne.toRingHom m (by simp [m]) (ratio 0 i).val=_
  rw [ratio_val,map_mul]
  rw [IsLocalization.Away.lift_eq]
  change atMOne (coordinate i)*
    (Localization.awayLift atMOne.toRingHom m (by simp [m])) (inverseCoordinate 0)=_
  have hi : (Localization.awayLift atMOne.toRingHom m (by simp [m])) (inverseCoordinate 0)=1 := by
    have h := congrArg (Localization.awayLift atMOne.toRingHom m
      (by simp [m])) (coordinate_mul_inverse 0)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atMOne (coordinate 0)*
      (Localization.awayLift atMOne.toRingHom m _) (inverseCoordinate 0)=1 at h
    simpa [atMOne_coordinate] using h
  rw [hi,mul_one,atMOne_coordinate]

/-- The affine generators interpreted as homogeneous ratios. -/
def infinityToChart : InfinityCoordinateRing →ₐ[ℚ] ChartRing 0 :=
  Ideal.Quotient.liftₐ infinityIdeal
    (MvPolynomial.aeval ![ratio 0 3,ratio 0 1,ratio 0 2]) (by
      have hker : infinityIdeal≤RingHom.ker
          (MvPolynomial.aeval ![ratio 0 3,ratio 0 1,ratio 0 2]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (infinityRelation i)=0
        fin_cases i
        all_goals simp [infinityRelation]
        all_goals apply HomogeneousLocalization.val_injective
        all_goals simp only [HomogeneousLocalization.val_sub,HomogeneousLocalization.val_pow,
          HomogeneousLocalization.val_mul,
          HomogeneousLocalization.val_zero,ratio_val]
        all_goals norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
        · have h := congrArg (algebraMap CoordinateRing (LocalizedRing 0)) u_sq
          simp only [map_add,map_mul,map_pow,map_ofNat] at h
          have hm := congrArg (fun t : LocalizedRing 0 => t^2) (coordinate_mul_inverse 0)
          linear_combination inverseCoordinate 0^2*h+15*hm
        · have h := congrArg (algebraMap CoordinateRing (LocalizedRing 0)) v_sq
          simp only [map_add,map_mul,map_pow,map_ofNat] at h
          have hm := congrArg (fun t : LocalizedRing 0 => t^2) (coordinate_mul_inverse 0)
          linear_combination inverseCoordinate 0^2*h+10*hm
      intro p hp
      exact hker hp)

@[simp] theorem infinityToChart_z : infinityToChart infinityZ=ratio 0 3 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 0)=_
  simp
@[simp] theorem infinityToChart_u : infinityToChart infinityU=ratio 0 1 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 1)=_
  simp
@[simp] theorem infinityToChart_v : infinityToChart infinityV=ratio 0 2 := by
  change (MvPolynomial.aeval _) (MvPolynomial.X 2)=_
  simp

/-- Setting m=1 after inserting homogeneous ratios fixes every affine coordinate. -/
theorem chartToInfinity_comp_infinityToChart :
    chartToInfinity.comp infinityToChart=AlgHom.id ℚ InfinityCoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToInfinity (infinityToChart infinityZ)=infinityZ
    rw [infinityToChart_z,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart infinityU)=infinityU
    rw [infinityToChart_u,chartToInfinity_ratio]
    rfl
  · change chartToInfinity (infinityToChart infinityV)=infinityV
    rw [infinityToChart_v,chartToInfinity_ratio]
    rfl

/-- Homogeneous coordinate ratios are fixed by dehomogenization and reconstruction. -/
theorem infinityToChart_comp_chartToInfinity :
    infinityToChart.comp chartToInfinity=AlgHom.id ℚ (ChartRing 0) := by
  apply chartAlgHom_ext 0
  intro i
  fin_cases i
  all_goals simp [ratio_self]

/-- Exact algebra isomorphism between the m-chart and the infinity affine quotient. -/
def mChartRingEquiv : mChartRing ≃ₐ[ℚ] InfinityCoordinateRing :=
  {chartToInfinity with
    invFun := infinityToChart
    left_inv := fun x => AlgHom.congr_fun infinityToChart_comp_chartToInfinity x
    right_inv := fun x => AlgHom.congr_fun chartToInfinity_comp_infinityToChart x}

/-- The affine scheme of the displayed infinity equations is the m≠0 open. -/
def mChartSchemeIso : mOpen.toScheme ≅ infinityScheme :=
  mChartIso ≪≫ Scheme.Spec.mapIso mChartRingEquiv.toRingEquiv.toCommRingCatIso.symm.op


end
end Z2Z4Rank6.ProjectiveBaseSchemeCharts
