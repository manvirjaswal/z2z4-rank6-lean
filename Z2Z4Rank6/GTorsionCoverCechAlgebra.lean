import Z2Z4Rank6.GTorsionCoverCechRanges
import Z2Z4Rank6.TwoChartEqualizer

/-! Two-chart restriction cokernels and compatible constants of both
signed torsion covers. All ring restrictions and their ranges are
proved. The comparison with sheaf cohomology is separate.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GTorsionCoverCechAlgebra
noncomputable section
open GTorsionCoverLaurent GTorsionCoverOverlap GTorsionCoverCechRanges

def differential (ε : Bool) :
    (GTorsionCoverAffine.CoordinateRing ε × GTorsionCoverInfinity.CoordinateRing ε) →ₗ[ℚ]
      FourLaurent := TwoChartEqualizer.difference (positiveRestriction ε) (negativeRestriction ε)

theorem differential_eq_coprod (ε : Bool) :
    differential ε = (positiveRestriction ε).coprod (-negativeRestriction ε) := by
  apply LinearMap.ext
  intro p
  funext i
  simp [differential,TwoChartEqualizer.difference,sub_eq_add_neg]

theorem differential_range (ε : Bool) : LinearMap.range (differential ε) = boundaryFour := by
  rw [differential_eq_coprod,LinearMap.range_coprod,LinearMap.range_neg,
    positiveRestriction_range,negativeRestriction_range]
  rfl

def coordinateCokernelEquiv (ε : Bool) :
    (FourLaurent ⧸ LinearMap.range (differential ε)) ≃ₗ[ℚ] (Fin 9 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ (differential_range ε)).trans quotientFourEquiv

theorem coordinate_cokernel_finrank (ε : Bool) :
    Module.finrank ℚ (FourLaurent ⧸ LinearMap.range (differential ε)) = 9 := by
  simpa using (coordinateCokernelEquiv ε).finrank_eq

def overlapDifferential (ε : Bool) :
    (GTorsionCoverAffine.CoordinateRing ε × GTorsionCoverInfinity.CoordinateRing ε) →ₗ[ℚ]
      OverlapRing ε := TwoChartEqualizer.difference (affineRestriction ε) (infinityRestriction ε).toLinearMap

theorem overlapDifferential_range (ε : Bool) :
    LinearMap.range (overlapDifferential ε) = LinearMap.range (affineRestriction ε) ⊔
      LinearMap.range (infinityRestriction ε).toLinearMap := by
  have he : overlapDifferential ε =
      (affineRestriction ε).coprod (-(infinityRestriction ε).toLinearMap) := by
    apply LinearMap.ext
    intro p
    simp [overlapDifferential,TwoChartEqualizer.difference,sub_eq_add_neg]
  rw [he,LinearMap.range_coprod,LinearMap.range_neg]

theorem coordinates_comp_overlapDifferential (ε : Bool) :
    (overlapCoordinates ε).toLinearMap.comp (overlapDifferential ε) = differential ε := by
  apply LinearMap.ext
  intro p
  funext i
  change overlapCoordinates ε (affineRestriction ε p.1 - infinityRestriction ε p.2) i =
    positiveRestriction ε p.1 i - negativeRestriction ε p.2 i
  rw [map_sub]
  rfl

theorem overlapDifferential_map_range (ε : Bool) :
    (LinearMap.range (overlapDifferential ε)).map (overlapCoordinates ε).toLinearMap =
      LinearMap.range (differential ε) := by
  rw [←LinearMap.range_comp,coordinates_comp_overlapDifferential]

def overlapCokernelEquiv (ε : Bool) :
    (OverlapRing ε ⧸ LinearMap.range (overlapDifferential ε)) ≃ₗ[ℚ] (Fin 9 → ℚ) :=
  (Submodule.Quotient.equiv (LinearMap.range (overlapDifferential ε))
    (LinearMap.range (differential ε)) (overlapCoordinates ε)
    (overlapDifferential_map_range ε)).trans (coordinateCokernelEquiv ε)

theorem overlap_cokernel_finrank (ε : Bool) :
    Module.finrank ℚ (OverlapRing ε ⧸ LinearMap.range (overlapDifferential ε)) = 9 := by
  simpa using (overlapCokernelEquiv ε).finrank_eq

theorem restriction_ranges (ε : Bool) :
    LinearMap.range (positiveRestriction ε) ⊓ LinearMap.range (negativeRestriction ε) =
      positiveFour ⊓ negativeFour := by
  rw [positiveRestriction_range,negativeRestriction_range]

def compatiblePairsEquiv (ε : Bool) : LinearMap.ker (differential ε) ≃ₗ[ℚ] ℚ :=
  ((TwoChartEqualizer.compatibleEquivIntersection (positiveRestriction ε) (negativeRestriction ε)
      (positiveRestriction_injective ε) (negativeRestriction_injective ε)).trans
    (LinearEquiv.ofEq _ _ (restriction_ranges ε))).trans intersectionFourEquiv

theorem finrank_compatible_pairs (ε : Bool) : Module.finrank ℚ (LinearMap.ker (differential ε)) = 1 := by
  simpa using (compatiblePairsEquiv ε).finrank_eq

end
end Z2Z4Rank6.GTorsionCoverCechAlgebra
