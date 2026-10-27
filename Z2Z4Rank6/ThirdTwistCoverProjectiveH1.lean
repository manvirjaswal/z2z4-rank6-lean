import Z2Z4Rank6.ThirdTwistCoverProjectiveCech
import Z2Z4Rank6.AffineCoverCohomologyTransport

/-! Structure-sheaf H1 of the third-twist base has dimension 5.
The hypothesis is the published two-affine-cover comparison. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveH1
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveSections
open StructureSheafCohomology ThirdTwistCoverOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def h1Equiv (h : AffineCoverStructureSheafCohomologyTheorem) :
    H1 (scheme) (structureMap)≃ₗ[ℚ](Fin 5→ℚ) :=
  AffineCoverCohomology.h1EquivOfCokernel h (scheme) (structureMap) (zOpen) (mOpen)
    (zOpen_isAffine) (mOpen_isAffine) (overlapOpen_isAffine) (two_chart_cover)
    (cechCokernelEquiv)

theorem h1_finiteDimensional (h : AffineCoverStructureSheafCohomologyTheorem) :
    FiniteDimensional ℚ (H1 (scheme) (structureMap)) :=
  Module.Finite.equiv (h1Equiv h).symm

theorem h1_finrank (h : AffineCoverStructureSheafCohomologyTheorem) :
    Module.finrank ℚ (H1 (scheme) (structureMap))=5 := by
  simpa using (h1Equiv h).finrank_eq

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveH1
