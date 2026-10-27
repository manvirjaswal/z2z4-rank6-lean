import Z2Z4Rank6.ThirdTwistCoverProjectiveStructure
import Z2Z4Rank6.WeightedProjectiveChartHelpers
import Z2Z4Rank6.WeightedHomogeneousChartTransition
import Z2Z4Rank6.ThirdTwistCoverEquationForms

/-! Weighted coordinate fractions on the two degree-one charts. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
noncomputable section
open scoped Classical
set_option maxRecDepth 4096
open ThirdTwistCoverProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev LocalizedRing  (k : Fin 5) := Localization.Away (coordinate k)
def ratio  (k : Fin 5) (hk : weights k=1) (i : Fin 5) : ChartRing k :=
  WeightedProjectiveChartHelpers.fraction (grading) (hk ▸ coordinate_degree k)
    (weights i) (coordinate i) (coordinate_degree i)
abbrev zRatio  := ratio 3 rfl
abbrev mRatio  := ratio 0 rfl
abbrev inverseCoordinate  (k : Fin 5) : LocalizedRing k :=
  IsLocalization.Away.invSelf (coordinate k)
theorem coordinate_mul_inverse  (k : Fin 5) :
    algebraMap (CoordinateRing) (LocalizedRing k) (coordinate k)*inverseCoordinate k=1 :=
  IsLocalization.Away.mul_invSelf _
theorem ratio_val  (k : Fin 5) (hk : weights k=1) (i : Fin 5) :
    (ratio k hk i).val=algebraMap (CoordinateRing) (LocalizedRing k)
      (coordinate i)*inverseCoordinate k^(weights i) :=
  WeightedProjectiveChartHelpers.fraction_val _ _ _ _ _
@[simp] theorem zRatio_self  : zRatio 3=1 :=
  WeightedProjectiveChartHelpers.fraction_self _ _
@[simp] theorem mRatio_self  : mRatio 0=1 :=
  WeightedProjectiveChartHelpers.fraction_self _ _

theorem chartRingHom_ext {S : Type*} [CommRing S]  (k : Fin 5) (hk : weights k=1)
    (F G : ChartRing k→+*S) (h : ∀i,F (ratio k hk i)=G (ratio k hk i)) : F=G :=
  WeightedProjectiveChartHelpers.ringHom_ext _ _ (coordinate) weights (coordinate_degree)
    (coordinate_adjoin) (degreeZero_eq_rat) F G h

open ThirdTwistCoverEquations

theorem ratio_root_sq  (k : Fin 5) (hk : weights k=1) (i : Fin 3) :
    ratio k hk (rootIndex i)^2=binary (ratio k hk 3) (ratio k hk 0) i := by
  apply HomogeneousLocalization.val_injective
  rw [←HomogeneousLocalization.algebraMap_apply,←HomogeneousLocalization.algebraMap_apply]
  rw [map_pow,ThirdTwistCoverEquations.map_binary]
  have hw : weights (rootIndex i)=rootWeight i := by fin_cases i <;> rfl
  simp only [HomogeneousLocalization.algebraMap_apply,ratio_val,hw,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
  have hr := congrArg (algebraMap (CoordinateRing) (LocalizedRing k)) (root_sq i)
  simp only [map_pow,ThirdTwistCoverEquations.map_binary] at hr
  exact ThirdTwistCoverEquations.normalized _ _ _ (inverseCoordinate k) i hr

theorem zRatio_root_sq  (i : Fin 3) :
    zRatio (rootIndex i)^2=binary 1 (zRatio 0) i := by
  simpa only [zRatio_self] using ratio_root_sq 3 rfl i
theorem mRatio_root_sq  (i : Fin 3) :
    mRatio (rootIndex i)^2=binary (mRatio 3) 1 i := by
  simpa only [mRatio_self] using ratio_root_sq 0 rfl i

theorem zRatio_u_sq  : zRatio 1^2=binary 1 (zRatio 0) 0 := zRatio_root_sq 0
theorem zRatio_v_sq  : zRatio 2^2=binary 1 (zRatio 0) 1 := zRatio_root_sq 1
theorem zRatio_r_sq  : zRatio 4^2=binary 1 (zRatio 0) 2 := zRatio_root_sq 2
theorem mRatio_u_sq  : mRatio 1^2=binary (mRatio 3) 1 0 := mRatio_root_sq 0
theorem mRatio_v_sq  : mRatio 2^2=binary (mRatio 3) 1 1 := mRatio_root_sq 1
theorem mRatio_r_sq  : mRatio 4^2=binary (mRatio 3) 1 2 := mRatio_root_sq 2
end
end Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
