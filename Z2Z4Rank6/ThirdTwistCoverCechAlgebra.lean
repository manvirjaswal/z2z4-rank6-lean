module

public import Z2Z4Rank6.ThirdTwistCoverCechRanges
public import Z2Z4Rank6.TwoChartEqualizer

@[expose] public section

/-! Two-chart restriction cokernels and compatible constants of both
third-twist base. All ring restrictions and their ranges are
proved. The comparison with sheaf cohomology is separate.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverCechAlgebra
noncomputable section
open ThirdTwistCoverLaurent ThirdTwistCoverOverlap ThirdTwistCoverCechRanges

def differential  :
    (ThirdTwistCoverAffine.CoordinateRing × ThirdTwistCoverInfinity.CoordinateRing) →ₗ[ℚ]
      EightLaurent := TwoChartEqualizer.difference (positiveRestriction) (negativeRestriction)

theorem differential_eq_coprod  :
    differential = (positiveRestriction).coprod (-negativeRestriction) := by
  apply LinearMap.ext
  intro p
  funext i
  simp [differential,TwoChartEqualizer.difference,sub_eq_add_neg]

theorem differential_range  : LinearMap.range (differential) = boundaryEight := by
  rw [differential_eq_coprod,LinearMap.range_coprod,LinearMap.range_neg,
    positiveRestriction_range,negativeRestriction_range]
  rfl

def coordinateCokernelEquiv  :
    (EightLaurent ⧸ LinearMap.range (differential)) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ (differential_range)).trans quotientEightEquiv

theorem coordinate_cokernel_finrank  :
    Module.finrank ℚ (EightLaurent ⧸ LinearMap.range (differential)) = 5 := by
  simpa using (coordinateCokernelEquiv).finrank_eq

def overlapDifferential  :
    (ThirdTwistCoverAffine.CoordinateRing × ThirdTwistCoverInfinity.CoordinateRing) →ₗ[ℚ]
      OverlapRing := TwoChartEqualizer.difference (affineRestriction) (infinityRestriction).toLinearMap

theorem overlapDifferential_range  :
    LinearMap.range (overlapDifferential) = LinearMap.range (affineRestriction) ⊔
      LinearMap.range (infinityRestriction).toLinearMap := by
  have he : overlapDifferential =
      (affineRestriction).coprod (-(infinityRestriction).toLinearMap) := by
    apply LinearMap.ext
    intro p
    simp [overlapDifferential,TwoChartEqualizer.difference,sub_eq_add_neg]
  rw [he,LinearMap.range_coprod,LinearMap.range_neg]

theorem coordinates_comp_overlapDifferential  :
    (overlapCoordinates).toLinearMap.comp (overlapDifferential) = differential := by
  apply LinearMap.ext
  intro p
  funext i
  change overlapCoordinates (affineRestriction p.1 - infinityRestriction p.2) i =
    positiveRestriction p.1 i - negativeRestriction p.2 i
  rw [map_sub]
  rfl

theorem overlapDifferential_map_range  :
    (LinearMap.range (overlapDifferential)).map (overlapCoordinates).toLinearMap =
      LinearMap.range (differential) := by
  rw [←LinearMap.range_comp,coordinates_comp_overlapDifferential]

def overlapCokernelEquiv  :
    (OverlapRing ⧸ LinearMap.range (overlapDifferential)) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  (Submodule.Quotient.equiv (LinearMap.range (overlapDifferential))
    (LinearMap.range (differential)) (overlapCoordinates)
    (overlapDifferential_map_range)).trans (coordinateCokernelEquiv)

theorem overlap_cokernel_finrank  :
    Module.finrank ℚ (OverlapRing ⧸ LinearMap.range (overlapDifferential)) = 5 := by
  simpa using (overlapCokernelEquiv).finrank_eq

theorem restriction_ranges  :
    LinearMap.range (positiveRestriction) ⊓ LinearMap.range (negativeRestriction) =
      positiveEight ⊓ negativeEight := by
  rw [positiveRestriction_range,negativeRestriction_range]

def compatiblePairsEquiv  : LinearMap.ker (differential) ≃ₗ[ℚ] ℚ :=
  ((TwoChartEqualizer.compatibleEquivIntersection (positiveRestriction) (negativeRestriction)
      (positiveRestriction_injective) (negativeRestriction_injective)).trans
    (LinearEquiv.ofEq _ _ (restriction_ranges))).trans intersectionEightEquiv

theorem finrank_compatible_pairs  : Module.finrank ℚ (LinearMap.ker (differential)) = 1 := by
  simpa using (compatiblePairsEquiv).finrank_eq

end
end Z2Z4Rank6.ThirdTwistCoverCechAlgebra
