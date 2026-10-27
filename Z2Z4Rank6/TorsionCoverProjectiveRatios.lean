import Z2Z4Rank6.TorsionCoverProjectiveStructure
import Z2Z4Rank6.WeightedProjectiveChartHelpers
import Z2Z4Rank6.WeightedHomogeneousChartTransition
import Z2Z4Rank6.TorsionCoverScaling

/-! Weighted coordinate fractions on the two degree-one charts. -/
namespace Z2Z4Rank6.TorsionCoverProjectiveCharts
noncomputable section
open scoped Classical
set_option maxRecDepth 4096
open TorsionCoverProjective
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

theorem zRatio_u_sq (ε : Bool) : zRatio ε 1^2=15*zRatio ε 0^2+1210 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  simp only [show weights (0:Fin 5)=1 from rfl,show weights (1:Fin 5)=1 from rfl,pow_one]
  exact TorsionCoverScaling.normalized_first _ _ _ _
    (by simpa only [map_pow,map_add,map_mul,map_ofNat] using
      congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε 3)) (u_sq ε))
    (coordinate_mul_inverse ε 3)

theorem zRatio_v_sq (ε : Bool) : zRatio ε 2^2=10*zRatio ε 0^2+1215 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  simp only [show weights (0:Fin 5)=1 from rfl,show weights (2:Fin 5)=1 from rfl,pow_one]
  exact TorsionCoverScaling.normalized_second _ _ _ _
    (by simpa only [map_pow,map_add,map_mul,map_ofNat] using
      congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε 3)) (v_sq ε))
    (coordinate_mul_inverse ε 3)

theorem mRatio_u_sq (ε : Bool) : mRatio ε 1^2=15+1210*mRatio ε 3^2 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  simp only [show weights (1:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
  exact TorsionCoverScaling.normalized_first_infinity _ _ _ _
    (by simpa only [map_pow,map_add,map_mul,map_ofNat] using
      congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε 0)) (u_sq ε))
    (coordinate_mul_inverse ε 0)

theorem mRatio_v_sq (ε : Bool) : mRatio ε 2^2=10+1215*mRatio ε 3^2 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  simp only [show weights (2:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
  exact TorsionCoverScaling.normalized_second_infinity _ _ _ _
    (by simpa only [map_pow,map_add,map_mul,map_ofNat] using
      congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε 0)) (v_sq ε))
    (coordinate_mul_inverse ε 0)

theorem val_rat (ε : Bool) (k : Fin 5) (q : ℚ) :
    (algebraMap ℚ (ChartRing ε k) q).val=algebraMap ℚ (LocalizedRing ε k) q := by
  exact RingHom.congr_fun (RingHom.ext_rat
    ((algebraMap (ChartRing ε k) (LocalizedRing ε k)).comp (algebraMap ℚ (ChartRing ε k)))
    (algebraMap ℚ (LocalizedRing ε k))) q

theorem ratio_r_sq (ε : Bool) (k : Fin 5) (hk : weights k=1) :
    ratio ε k hk 4^2=algebraMap ℚ (ChartRing ε k) (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (ratio ε k hk 3) (ratio ε k hk 0)*
      HeightInvariantForms.binaryB (ratio ε k hk 3) (ratio ε k hk 0) := by
  apply HomogeneousLocalization.val_injective
  rw [←HomogeneousLocalization.algebraMap_apply,←HomogeneousLocalization.algebraMap_apply]
  rw [map_pow,map_mul,map_mul,TorsionCoverScaling.map_binaryA,TorsionCoverScaling.map_binaryB]
  simp only [HomogeneousLocalization.algebraMap_apply,ratio_val,val_rat]
  have hr := congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε k)) (r_sq ε)
  simp only [map_pow,map_mul,TorsionCoverScaling.map_binaryA,TorsionCoverScaling.map_binaryB] at hr
  have hq : algebraMap (CoordinateRing ε) (LocalizedRing ε k)
      (algebraMap ℚ (CoordinateRing ε) (TorsionHyperelliptic.sign ε))=
      algebraMap ℚ (LocalizedRing ε k) (TorsionHyperelliptic.sign ε) :=
    RingHom.congr_fun (RingHom.ext_rat
      ((algebraMap (CoordinateRing ε) (LocalizedRing ε k)).comp (algebraMap ℚ (CoordinateRing ε)))
      (algebraMap ℚ (LocalizedRing ε k))) _
  rw [hq] at hr
  simpa only [show weights (4:Fin 5)=4 from rfl,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one] using
    TorsionCoverScaling.normalized_third _ _ _ (inverseCoordinate ε k) _ hr

theorem zRatio_r_sq (ε : Bool) :
    zRatio ε 4^2=algebraMap ℚ (zChartRing ε) (TorsionHyperelliptic.sign ε)*
      a (zRatio ε 0)*b (zRatio ε 0) := by
  simpa only [zRatio_self,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB,a,b,mul_one]
    using ratio_r_sq ε 3 rfl
theorem mRatio_r_sq (ε : Bool) :
    mRatio ε 4^2=algebraMap ℚ (mChartRing ε) (TorsionHyperelliptic.sign ε)*
      HeightInvariantForms.binaryA (mRatio ε 3) 1*HeightInvariantForms.binaryB (mRatio ε 3) 1 := by
  simpa only [mRatio_self] using ratio_r_sq ε 0 rfl

end
end Z2Z4Rank6.TorsionCoverProjectiveCharts
