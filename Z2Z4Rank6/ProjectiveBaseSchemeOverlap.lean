module

public import Z2Z4Rank6.ProjectiveBaseSchemeStructure
public import Z2Z4Rank6.ProjectiveBaseSchemeChartGenerators
public import Z2Z4Rank6.HomogeneousChartTransition
public import Z2Z4Rank6.InfinityBaseOverlapMap

@[expose] public section

/-!
# The homogeneous overlap is the affine localization

The D(zm) coordinate ring is the localization of the D(z) ring at m/z.
The explicit z-chart isomorphism sends m/z to the affine m, so
localization uniqueness identifies it with A[m⁻¹]. All maps are
ring maps and both chart restrictions will be tracked explicitly.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeSections
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev HomogeneousOverlap := HomogeneousLocalization.Away grading (z*m)
abbrev ActualOverlap := AffineBaseFunctionFieldIso.OverlapRing

def zAway : zChartRing →+* HomogeneousOverlap :=
  HomogeneousLocalization.awayMap grading (coordinate_degree 0) rfl

def mAway : mChartRing →+* HomogeneousOverlap :=
  HomogeneousLocalization.awayMap grading (coordinate_degree 3) (mul_comm z m)

instance overlapChartAlgebra : Algebra zChartRing HomogeneousOverlap := zAway.toAlgebra

theorem localizationElement_eq :
    HomogeneousLocalization.Away.isLocalizationElem (coordinate_degree 3)
      (coordinate_degree 0)=ratio 3 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem,ratio,
    HomogeneousLocalization.Away.val_mk,pow_one]

instance homogeneousOverlapLocalization : IsLocalization.Away (ratio 3 0) HomogeneousOverlap := by
  rw [←localizationElement_eq]
  exact HomogeneousLocalization.Away.isLocalization_mul (coordinate_degree 3)
    (coordinate_degree 0) (rfl : z*m=z*m) (by decide : (1:ℕ)≠0)

theorem zChart_map_denominators :
    (Submonoid.powers (ratio 3 0)).map zChartRingEquiv.toRingEquiv.toMonoidHom=
      Submonoid.powers AffineBaseScheme.m := by
  rw [Submonoid.map_powers]
  congr 1
  change chartToAffine (ratio 3 0)=AffineBaseScheme.m
  simp [chartToAffine_ratio]

/-- Canonical localization equivalence from the projective overlap
ring to the affine coordinate localization. -/
def homogeneousOverlapEquiv : HomogeneousOverlap ≃+* ActualOverlap :=
  IsLocalization.ringEquivOfRingEquiv HomogeneousOverlap ActualOverlap zChartRingEquiv.toRingEquiv
    zChart_map_denominators

@[simp] theorem homogeneousOverlapEquiv_zAway (x : zChartRing) :
    homogeneousOverlapEquiv (zAway x)=algebraMap AffineBaseScheme.CoordinateRing ActualOverlap
      (zChartRingEquiv x) :=
  IsLocalization.ringEquivOfRingEquiv_eq zChart_map_denominators x

/-- The exact transition identity between the two homogeneous coordinate charts. -/
theorem mAway_ratio_mul (i : Fin 4) :
    mAway (ratio 0 i)*zAway (ratio 3 0)=zAway (ratio 3 i) := by
  exact HomogeneousChartTransition.transition grading z m (coordinate i)
    (coordinate_degree 3) (coordinate_degree 0) (coordinate_degree i)

/-- The m-chart transition in the affine overlap. -/
theorem homogeneousOverlapEquiv_mAway_ratio (i : Fin 4) :
    homogeneousOverlapEquiv (mAway (ratio 0 i))=
      algebraMap AffineBaseScheme.CoordinateRing ActualOverlap
        (![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1] i)*
          AffineBaseFunctionFieldIso.inverseM := by
  have h := congrArg homogeneousOverlapEquiv (mAway_ratio_mul i)
  simp only [map_mul,homogeneousOverlapEquiv_zAway] at h
  change homogeneousOverlapEquiv (mAway (ratio 0 i))*
    algebraMap AffineBaseScheme.CoordinateRing ActualOverlap (chartToAffine (ratio 3 0))=
      algebraMap AffineBaseScheme.CoordinateRing ActualOverlap (chartToAffine (ratio 3 i)) at h
  rw [chartToAffine_ratio,chartToAffine_ratio] at h
  have h0 : ![AffineBaseScheme.m,AffineBaseScheme.u,AffineBaseScheme.v,1] (0:Fin 4)=
      AffineBaseScheme.m := rfl
  rw [h0] at h
  calc
    _=homogeneousOverlapEquiv (mAway (ratio 0 i))*
        (algebraMap AffineBaseScheme.CoordinateRing ActualOverlap AffineBaseScheme.m*
          AffineBaseFunctionFieldIso.inverseM) := by rw [AffineBaseFunctionFieldIso.m_mul_inverseM,mul_one]
    _=_ := by rw [←mul_assoc,h]

def mToActualOverlap : mChartRing →+* ActualOverlap :=
  homogeneousOverlapEquiv.toRingHom.comp mAway

/-- Both affine chart restriction maps agree on every coordinate. -/
theorem mToActualOverlap_eq :
    mToActualOverlap=AffineBaseFunctionFieldIso.infinityRestriction.toRingHom.comp
      mChartRingEquiv.toRingEquiv.toRingHom := by
  apply chartRingHom_ext (S:=ActualOverlap) 0 mToActualOverlap
    (AffineBaseFunctionFieldIso.infinityRestriction.toRingHom.comp mChartRingEquiv.toRingEquiv.toRingHom)
  intro i
  change homogeneousOverlapEquiv (mAway (ratio 0 i))=
    AffineBaseFunctionFieldIso.infinityRestriction (chartToInfinity (ratio 0 i))
  rw [homogeneousOverlapEquiv_mAway_ratio,chartToInfinity_ratio]
  fin_cases i
  all_goals simp [AffineBaseFunctionFieldIso.m_mul_inverseM]

end
end Z2Z4Rank6.ProjectiveBaseSchemeSections
