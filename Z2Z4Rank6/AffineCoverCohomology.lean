import Z2Z4Rank6.StructureSheafCohomology
import Mathlib.AlgebraicGeometry.AffineScheme
import Z2Z4Rank6.AffineCoverModuleQuotient

/-!
# Generic two-affine-cover comparison with structure-sheaf H1

Stacks
Lemma 30.2.6 (tag 01XD) computes quasi-coherent cohomology by an affine cover.
The exact two-open cokernel form follows directly from Mayer–Vietoris,
Lemma 20.8.2 (tag 01EB), and affine vanishing, Lemma 30.2.2 (tag 01XB).
The Ext1 target is the standard first sheaf cohomology by
Lemma 20.5.1 (tag 0B3A) and Lemma 21.12.4 (tag 03FD).

This is a direct corollary of these statements, not a numbered theorem in the source.

-/
namespace Z2Z4Rank6.AffineCoverCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory
open StructureSheafCohomology

/-- The two-open restriction differential for the structure sheaf. -/
def differential (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens) :
    sectionModule X s U × sectionModule X s V →ₗ[ℚ] sectionModule X s (U⊓V) :=
  AffineCoverModuleQuotient.difference
    (restriction X s U (U⊓V) inf_le_left) (restriction X s V (U⊓V) inf_le_right)

/-- The restriction-map cokernel, carrying its rational module structure. -/
abbrev Cokernel (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens) :=
  sectionModule X s (U⊓V) ⧸ LinearMap.range (differential X s U V)

theorem differential_apply (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens)
    (x : sectionModule X s U) (y : sectionModule X s V) :
    differential X s U V (x,y)=restriction X s U (U⊓V) inf_le_left x-
      restriction X s V (U⊓V) inf_le_right y :=
  AffineCoverModuleQuotient.difference_apply _ _ _ _

theorem differential_range (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens) :
    LinearMap.range (differential X s U V)=
      LinearMap.range (restriction X s U (U⊓V) inf_le_left) ⊔
        LinearMap.range (restriction X s V (U⊓V) inf_le_right) :=
  AffineCoverModuleQuotient.range_difference _ _

end
end Z2Z4Rank6.AffineCoverCohomology

namespace Z2Z4Rank6
open AlgebraicGeometry CategoryTheory

/-- Published two-affine-cover comparison, specialized to the
structure sheaf over Q. -/
def AffineCoverStructureSheafCohomologyTheorem : Prop :=
  ∀(X : Scheme.{0})(s : X⟶StructureSheafCohomology.Base)(U V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U⊓V) → U⊔V=⊤ →
      Nonempty (AffineCoverCohomology.Cokernel X s U V ≃ₗ[ℚ]
        StructureSheafCohomology.H1 X s)

namespace AffineCoverCohomology
noncomputable section

theorem comparison (h : AffineCoverStructureSheafCohomologyTheorem)
    (X : Scheme.{0})(s : X⟶StructureSheafCohomology.Base)(U V : X.Opens)
    (hU : IsAffineOpen U)(hV : IsAffineOpen V)(hUV : IsAffineOpen (U⊓V))(hcover : U⊔V=⊤) :
    Nonempty (Cokernel X s U V ≃ₗ[ℚ] StructureSheafCohomology.H1 X s) :=
  h X s U V hU hV hUV hcover

/-- Select the published comparison. -/
def comparisonEquiv (h : AffineCoverStructureSheafCohomologyTheorem)
    (X : Scheme.{0})(s : X⟶StructureSheafCohomology.Base)(U V : X.Opens)
    (hU : IsAffineOpen U)(hV : IsAffineOpen V)(hUV : IsAffineOpen (U⊓V))(hcover : U⊔V=⊤) :
    Cokernel X s U V ≃ₗ[ℚ] StructureSheafCohomology.H1 X s :=
  Classical.choice (comparison h X s U V hU hV hUV hcover)

end
end AffineCoverCohomology
end Z2Z4Rank6
