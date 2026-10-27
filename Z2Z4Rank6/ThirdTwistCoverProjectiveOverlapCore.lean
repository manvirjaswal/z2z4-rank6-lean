import Z2Z4Rank6.ThirdTwistCoverProjectiveCharts
import Z2Z4Rank6.ThirdTwistCoverOverlap

/-! The weighted Proj overlap and both affine restriction maps. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev HomogeneousOverlap  := HomogeneousLocalization.Away (grading) (z*m)
abbrev ActualOverlap  := ThirdTwistCoverOverlap.OverlapRing

def zAway  : zChartRing→+*HomogeneousOverlap :=
  HomogeneousLocalization.awayMap (grading) (coordinate_degree 0) rfl
def mAway  : mChartRing→+*HomogeneousOverlap :=
  HomogeneousLocalization.awayMap (grading) (coordinate_degree 3) (mul_comm (z) (m))
instance overlapChartAlgebra  : Algebra (zChartRing) (HomogeneousOverlap) :=
  (zAway).toAlgebra

theorem localizationElement_eq  :
    HomogeneousLocalization.Away.isLocalizationElem (coordinate_degree 3)
      (coordinate_degree 0)=zRatio 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,ratio,
    WeightedProjectiveChartHelpers.fraction,HomogeneousLocalization.Away.val_mk,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
instance homogeneousOverlapLocalization  :
    IsLocalization.Away (zRatio 0) (HomogeneousOverlap) := by
  rw [←localizationElement_eq]
  exact HomogeneousLocalization.Away.isLocalization_mul (coordinate_degree 3)
    (coordinate_degree 0) (rfl : z*m=z*m) (by decide : (1:ℕ)≠0)

theorem zChart_map_denominators  :
    (Submonoid.powers (zRatio 0)).map (zChartRingEquiv).toRingEquiv.toMonoidHom=
      Submonoid.powers (ThirdTwistCoverAffine.m) := by
  rw [Submonoid.map_powers]
  congr 1
  change chartToAffine (zRatio 0)=ThirdTwistCoverAffine.m
  simp

def homogeneousOverlapEquiv  : HomogeneousOverlap≃+*ActualOverlap :=
  IsLocalization.ringEquivOfRingEquiv (HomogeneousOverlap) (ActualOverlap)
    (zChartRingEquiv).toRingEquiv (zChart_map_denominators)
@[simp] theorem homogeneousOverlapEquiv_zAway  (x : zChartRing) :
    homogeneousOverlapEquiv (zAway x)=
      algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap) (zChartRingEquiv x) :=
  IsLocalization.ringEquivOfRingEquiv_eq (zChart_map_denominators) x

theorem mAway_ratio_mul  (i : Fin 5) :
    mAway (mRatio i)*zAway (zRatio 0)^(weights i)=zAway (zRatio i) :=
  WeightedHomogeneousChartTransition.transition (grading) (z) (m) (coordinate i)
    (weights i) (coordinate_degree 3) (coordinate_degree 0) (by simpa using coordinate_degree i)

theorem homogeneousOverlapEquiv_mAway_ratio  (i : Fin 5) :
    homogeneousOverlapEquiv (mAway (mRatio i))=
      algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
        (![ThirdTwistCoverAffine.m,ThirdTwistCoverAffine.u,ThirdTwistCoverAffine.v,1,ThirdTwistCoverAffine.r] i)*
          ThirdTwistCoverOverlap.inverseM^(weights i) := by
  have h := congrArg (homogeneousOverlapEquiv) (mAway_ratio_mul i)
  simp only [map_mul,map_pow,homogeneousOverlapEquiv_zAway] at h
  change homogeneousOverlapEquiv (mAway (mRatio i))*
    algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
      (chartToAffine (zRatio 0))^(weights i)=
    algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
      (chartToAffine (zRatio i)) at h
  rw [chartToAffine_ratio,chartToAffine_ratio] at h
  change homogeneousOverlapEquiv (mAway (mRatio i))*
    algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
      (ThirdTwistCoverAffine.m)^(weights i)=_ at h
  have hi : (algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
      (ThirdTwistCoverAffine.m))^(weights i)*ThirdTwistCoverOverlap.inverseM^(weights i)=1 :=
    ((Commute.all (algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
      (ThirdTwistCoverAffine.m)) (ThirdTwistCoverOverlap.inverseM)).mul_pow (weights i)).symm.trans
      ((congrArg (fun x : ActualOverlap => x^(weights i))
        (ThirdTwistCoverOverlap.m_mul_inverseM)).trans (one_pow _))
  calc
    _=homogeneousOverlapEquiv (mAway (mRatio i))*
        ((algebraMap (ThirdTwistCoverAffine.CoordinateRing) (ActualOverlap)
          (ThirdTwistCoverAffine.m))^(weights i)*ThirdTwistCoverOverlap.inverseM^(weights i)) := by
      rw [hi,mul_one]
    _=_ := by rw [←mul_assoc,h]

def mToActualOverlap  : mChartRing→+*ActualOverlap :=
  (homogeneousOverlapEquiv).toRingHom.comp (mAway)

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveSections
