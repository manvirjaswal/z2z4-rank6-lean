import Z2Z4Rank6.GTorsionCoverProjectiveCech
import Z2Z4Rank6.AffineCoverCohomologyTransport

/-! Structure-sheaf H1 of both signed covers has dimension 9.
The hypothesis is the published two-affine-cover comparison. -/
namespace Z2Z4Rank6.GTorsionCoverProjectiveH1
noncomputable section
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverProjectiveSections
open StructureSheafCohomology GTorsionCoverOverlap
variable (ε : Bool)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def h1Equiv (h : AffineCoverStructureSheafCohomologyTheorem) :
    H1 (scheme ε) (structureMap ε)≃ₗ[ℚ](Fin 9→ℚ) :=
  AffineCoverCohomology.h1EquivOfCokernel h (scheme ε) (structureMap ε) (zOpen ε) (mOpen ε)
    (zOpen_isAffine ε) (mOpen_isAffine ε) (overlapOpen_isAffine ε) (two_chart_cover ε)
    (cechCokernelEquiv ε)

theorem h1_finiteDimensional (h : AffineCoverStructureSheafCohomologyTheorem) :
    FiniteDimensional ℚ (H1 (scheme ε) (structureMap ε)) :=
  Module.Finite.equiv (h1Equiv ε h).symm

theorem h1_finrank (h : AffineCoverStructureSheafCohomologyTheorem) :
    Module.finrank ℚ (H1 (scheme ε) (structureMap ε))=9 := by
  simpa using (h1Equiv ε h).finrank_eq

end
end Z2Z4Rank6.GTorsionCoverProjectiveH1
