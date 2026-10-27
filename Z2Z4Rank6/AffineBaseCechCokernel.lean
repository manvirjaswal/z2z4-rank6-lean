import Z2Z4Rank6.AffineBaseRestrictionInjective
import Z2Z4Rank6.TwoChartEqualizer

/-! The cokernel of the two chart restrictions is one-dimensional.
Both source rings, the localized overlap, its Laurent coordinates and both
restriction ranges are constructed and proved. Identification with sheaf H¹
is a separate geometric comparison. -/
namespace Z2Z4Rank6.AffineBaseCechCokernel
noncomputable section
open AffineBaseFunctionFieldIso AffineBaseCechRanges NegativeLaurentRange LaurentCechQuotient

def differential :
    (CoordinateRing×ProjectiveBaseSchemeCharts.InfinityCoordinateRing)→ₗ[ℚ]FourLaurent :=
  TwoChartEqualizer.difference positiveRestriction negativeRestriction

theorem differential_eq_coprod : differential=positiveRestriction.coprod (-negativeRestriction) := by
  apply LinearMap.ext
  intro p
  funext i
  simp [differential,TwoChartEqualizer.difference,sub_eq_add_neg]

theorem differential_range : LinearMap.range differential=boundaryFour := by
  rw [differential_eq_coprod,LinearMap.range_coprod,LinearMap.range_neg,
    positiveRestriction_range,negativeRestriction_range]
  rfl

def coordinateCokernelEquiv : (FourLaurent⧸LinearMap.range differential)≃ₗ[ℚ]ℚ :=
  (Submodule.quotEquivOfEq _ _ differential_range).trans quotientFourEquiv

theorem coordinate_cokernel_finrank : Module.finrank ℚ (FourLaurent⧸LinearMap.range differential)=1 := by
  simpa using coordinateCokernelEquiv.finrank_eq

/-- The difference map takes values in the localized overlap,
before choosing Laurent coordinates. -/
def overlapDifferential :
    (CoordinateRing×ProjectiveBaseSchemeCharts.InfinityCoordinateRing)→ₗ[ℚ]OverlapRing :=
  TwoChartEqualizer.difference affineRestriction infinityRestriction.toLinearMap

theorem coordinates_comp_overlapDifferential :
    overlapCoordinates.toLinearMap.comp overlapDifferential=differential := by
  apply LinearMap.ext
  intro p
  funext i
  change overlapCoordinates (affineRestriction p.1-infinityRestriction p.2) i=
    positiveRestriction p.1 i-negativeRestriction p.2 i
  rw [map_sub]
  rfl

theorem overlapDifferential_map_range :
    (LinearMap.range overlapDifferential).map overlapCoordinates.toLinearMap=LinearMap.range differential := by
  rw [←LinearMap.range_comp,coordinates_comp_overlapDifferential]

def overlapCokernelEquiv : (OverlapRing⧸LinearMap.range overlapDifferential)≃ₗ[ℚ]ℚ :=
  (Submodule.Quotient.equiv (LinearMap.range overlapDifferential)
    (LinearMap.range differential) overlapCoordinates overlapDifferential_map_range).trans coordinateCokernelEquiv

/-- The algebraic Cech quotient of the two affine coordinate rings
and their overlap has dimension one. -/
theorem overlap_cokernel_finrank :
    Module.finrank ℚ (OverlapRing⧸LinearMap.range overlapDifferential)=1 := by
  simpa using overlapCokernelEquiv.finrank_eq
end
end Z2Z4Rank6.AffineBaseCechCokernel
