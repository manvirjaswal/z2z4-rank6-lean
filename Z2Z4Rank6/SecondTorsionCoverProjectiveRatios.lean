module

public import Z2Z4Rank6.SecondTorsionCoverProjectiveStructure
public import Z2Z4Rank6.WeightedProjectiveChartHelpers
public import Z2Z4Rank6.WeightedHomogeneousChartTransition
public import Z2Z4Rank6.SecondTorsionCoverEquationForms

@[expose] public section

/-! Weighted coordinate fractions on the two degree-one charts. -/
namespace Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
noncomputable section
open scoped Classical
set_option maxRecDepth 4096
open SecondTorsionCoverProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev LocalizedRing (ε : Bool) (k : Fin 5) := Localization.Away (coordinate ε k)
def ratio (ε : Bool) (k : Fin 5) (hk : weights k=1) (i : Fin 5) : ChartRing ε k :=
  WeightedProjectiveChartHelpers.fraction (grading ε) (hk ▸ coordinate_degree ε k)
    (weights i) (coordinate ε i) (coordinate_degree ε i)
abbrev zRatio (ε : Bool) := ratio ε 3 rfl
abbrev mRatio (ε : Bool) := ratio ε 0 rfl
abbrev inverseCoordinate (ε : Bool) (k : Fin 5) : LocalizedRing ε k :=
  IsLocalization.Away.invSelf (coordinate ε k)
theorem coordinate_mul_inverse (ε : Bool) (k : Fin 5) :
    algebraMap (CoordinateRing ε) (LocalizedRing ε k) (coordinate ε k)*inverseCoordinate ε k=1 :=
  IsLocalization.Away.mul_invSelf _
theorem ratio_val (ε : Bool) (k : Fin 5) (hk : weights k=1) (i : Fin 5) :
    (ratio ε k hk i).val=algebraMap (CoordinateRing ε) (LocalizedRing ε k)
      (coordinate ε i)*inverseCoordinate ε k^(weights i) :=
  WeightedProjectiveChartHelpers.fraction_val _ _ _ _ _
@[simp] theorem zRatio_self (ε : Bool) : zRatio ε 3=1 :=
  WeightedProjectiveChartHelpers.fraction_self _ _
@[simp] theorem mRatio_self (ε : Bool) : mRatio ε 0=1 :=
  WeightedProjectiveChartHelpers.fraction_self _ _

theorem chartRingHom_ext {S : Type*} [CommRing S] (ε : Bool) (k : Fin 5) (hk : weights k=1)
    (F G : ChartRing ε k→+*S) (h : ∀i,F (ratio ε k hk i)=G (ratio ε k hk i)) : F=G :=
  WeightedProjectiveChartHelpers.ringHom_ext _ _ (coordinate ε) weights (coordinate_degree ε)
    (coordinate_adjoin ε) (degreeZero_eq_rat ε) F G h

open SecondTorsionCoverEquations

theorem ratio_root_sq (ε : Bool) (k : Fin 5) (hk : weights k=1) (i : Fin 3) :
    ratio ε k hk (rootIndex i)^2=binary ε (ratio ε k hk 3) (ratio ε k hk 0) i := by
  apply HomogeneousLocalization.val_injective
  rw [←HomogeneousLocalization.algebraMap_apply,←HomogeneousLocalization.algebraMap_apply]
  rw [map_pow,SecondTorsionCoverEquations.map_binary]
  have hw : weights (rootIndex i)=rootWeight i := by fin_cases i <;> rfl
  simp only [HomogeneousLocalization.algebraMap_apply,ratio_val,hw,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
  have hr := congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε k)) (root_sq ε i)
  simp only [map_pow,SecondTorsionCoverEquations.map_binary] at hr
  exact SecondTorsionCoverEquations.normalized ε _ _ _ (inverseCoordinate ε k) i hr

theorem zRatio_root_sq (ε : Bool) (i : Fin 3) :
    zRatio ε (rootIndex i)^2=binary ε 1 (zRatio ε 0) i := by
  simpa only [zRatio_self] using ratio_root_sq ε 3 rfl i
theorem mRatio_root_sq (ε : Bool) (i : Fin 3) :
    mRatio ε (rootIndex i)^2=binary ε (mRatio ε 3) 1 i := by
  simpa only [mRatio_self] using ratio_root_sq ε 0 rfl i

theorem zRatio_u_sq (ε : Bool) : zRatio ε 1^2=binary ε 1 (zRatio ε 0) 0 := zRatio_root_sq ε 0
theorem zRatio_v_sq (ε : Bool) : zRatio ε 2^2=binary ε 1 (zRatio ε 0) 1 := zRatio_root_sq ε 1
theorem zRatio_r_sq (ε : Bool) : zRatio ε 4^2=binary ε 1 (zRatio ε 0) 2 := zRatio_root_sq ε 2
theorem mRatio_u_sq (ε : Bool) : mRatio ε 1^2=binary ε (mRatio ε 3) 1 0 := mRatio_root_sq ε 0
theorem mRatio_v_sq (ε : Bool) : mRatio ε 2^2=binary ε (mRatio ε 3) 1 1 := mRatio_root_sq ε 1
theorem mRatio_r_sq (ε : Bool) : mRatio ε 4^2=binary ε (mRatio ε 3) 1 2 := mRatio_root_sq ε 2
end
end Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
