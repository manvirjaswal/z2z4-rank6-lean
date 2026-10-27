module

public import Z2Z4Rank6.SecondTorsionCoverProjectiveCharts
public import Z2Z4Rank6.SecondTorsionCoverOverlap

@[expose] public section

/-! The weighted Proj overlap and both affine restriction maps. -/
namespace Z2Z4Rank6.SecondTorsionCoverProjectiveSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open SecondTorsionCoverProjective SecondTorsionCoverProjectiveCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev HomogeneousOverlap (ε : Bool) := HomogeneousLocalization.Away (grading ε) (z ε*m ε)
abbrev ActualOverlap (ε : Bool) := SecondTorsionCoverOverlap.OverlapRing ε

def zAway (ε : Bool) : zChartRing ε→+*HomogeneousOverlap ε :=
  HomogeneousLocalization.awayMap (grading ε) (coordinate_degree ε 0) rfl
def mAway (ε : Bool) : mChartRing ε→+*HomogeneousOverlap ε :=
  HomogeneousLocalization.awayMap (grading ε) (coordinate_degree ε 3) (mul_comm (z ε) (m ε))
instance overlapChartAlgebra (ε : Bool) : Algebra (zChartRing ε) (HomogeneousOverlap ε) :=
  (zAway ε).toAlgebra

theorem localizationElement_eq (ε : Bool) :
    HomogeneousLocalization.Away.isLocalizationElem (coordinate_degree ε 3)
      (coordinate_degree ε 0)=zRatio ε 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,ratio,
    WeightedProjectiveChartHelpers.fraction,HomogeneousLocalization.Away.val_mk,
    show weights (0:Fin 5)=1 from rfl,show weights (3:Fin 5)=1 from rfl,pow_one]
instance homogeneousOverlapLocalization (ε : Bool) :
    IsLocalization.Away (zRatio ε 0) (HomogeneousOverlap ε) := by
  rw [←localizationElement_eq]
  exact HomogeneousLocalization.Away.isLocalization_mul (coordinate_degree ε 3)
    (coordinate_degree ε 0) (rfl : z ε*m ε=z ε*m ε) (by decide : (1:ℕ)≠0)

theorem zChart_map_denominators (ε : Bool) :
    (Submonoid.powers (zRatio ε 0)).map (zChartRingEquiv ε).toRingEquiv.toMonoidHom=
      Submonoid.powers (SecondTorsionCoverAffine.m ε) := by
  rw [Submonoid.map_powers]
  congr 1
  change chartToAffine ε (zRatio ε 0)=SecondTorsionCoverAffine.m ε
  simp

def homogeneousOverlapEquiv (ε : Bool) : HomogeneousOverlap ε≃+*ActualOverlap ε :=
  IsLocalization.ringEquivOfRingEquiv (HomogeneousOverlap ε) (ActualOverlap ε)
    (zChartRingEquiv ε).toRingEquiv (zChart_map_denominators ε)
@[simp] theorem homogeneousOverlapEquiv_zAway (ε : Bool) (x : zChartRing ε) :
    homogeneousOverlapEquiv ε (zAway ε x)=
      algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε) (zChartRingEquiv ε x) :=
  IsLocalization.ringEquivOfRingEquiv_eq (zChart_map_denominators ε) x

theorem mAway_ratio_mul (ε : Bool) (i : Fin 5) :
    mAway ε (mRatio ε i)*zAway ε (zRatio ε 0)^(weights i)=zAway ε (zRatio ε i) :=
  WeightedHomogeneousChartTransition.transition (grading ε) (z ε) (m ε) (coordinate ε i)
    (weights i) (coordinate_degree ε 3) (coordinate_degree ε 0) (by simpa using coordinate_degree ε i)

theorem homogeneousOverlapEquiv_mAway_ratio (ε : Bool) (i : Fin 5) :
    homogeneousOverlapEquiv ε (mAway ε (mRatio ε i))=
      algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
        (![SecondTorsionCoverAffine.m ε,SecondTorsionCoverAffine.u ε,SecondTorsionCoverAffine.v ε,1,SecondTorsionCoverAffine.r ε] i)*
          SecondTorsionCoverOverlap.inverseM ε^(weights i) := by
  have h := congrArg (homogeneousOverlapEquiv ε) (mAway_ratio_mul ε i)
  simp only [map_mul,map_pow,homogeneousOverlapEquiv_zAway] at h
  change homogeneousOverlapEquiv ε (mAway ε (mRatio ε i))*
    algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
      (chartToAffine ε (zRatio ε 0))^(weights i)=
    algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
      (chartToAffine ε (zRatio ε i)) at h
  rw [chartToAffine_ratio,chartToAffine_ratio] at h
  change homogeneousOverlapEquiv ε (mAway ε (mRatio ε i))*
    algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
      (SecondTorsionCoverAffine.m ε)^(weights i)=_ at h
  have hi : (algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
      (SecondTorsionCoverAffine.m ε))^(weights i)*SecondTorsionCoverOverlap.inverseM ε^(weights i)=1 :=
    ((Commute.all (algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
      (SecondTorsionCoverAffine.m ε)) (SecondTorsionCoverOverlap.inverseM ε)).mul_pow (weights i)).symm.trans
      ((congrArg (fun x : ActualOverlap ε => x^(weights i))
        (SecondTorsionCoverOverlap.m_mul_inverseM ε)).trans (one_pow _))
  calc
    _=homogeneousOverlapEquiv ε (mAway ε (mRatio ε i))*
        ((algebraMap (SecondTorsionCoverAffine.CoordinateRing ε) (ActualOverlap ε)
          (SecondTorsionCoverAffine.m ε))^(weights i)*SecondTorsionCoverOverlap.inverseM ε^(weights i)) := by
      rw [hi,mul_one]
    _=_ := by rw [←mul_assoc,h]

def mToActualOverlap (ε : Bool) : mChartRing ε→+*ActualOverlap ε :=
  (homogeneousOverlapEquiv ε).toRingHom.comp (mAway ε)

end
end Z2Z4Rank6.SecondTorsionCoverProjectiveSections
