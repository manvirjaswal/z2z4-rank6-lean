import Z2Z4Rank6.AffineCoverCohomology

/-! Compose the generic sheaf comparison before instantiating a large scheme.
This keeps kernel checking of geometric applications bounded. -/
namespace Z2Z4Rank6.AffineCoverCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory

def h1EquivOfCokernel (h : AffineCoverStructureSheafCohomologyTheorem)
    (X : Scheme.{0}) (s : X ⟶ StructureSheafCohomology.Base) (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hcover : U ⊔ V = ⊤)
    {M : Type} [AddCommGroup M] [Module ℚ M]
    (e : Cokernel X s U V ≃ₗ[ℚ] M) :
    StructureSheafCohomology.H1 X s ≃ₗ[ℚ] M :=
  (comparisonEquiv h X s U V hU hV hUV hcover).symm.trans e

end
end Z2Z4Rank6.AffineCoverCohomology
