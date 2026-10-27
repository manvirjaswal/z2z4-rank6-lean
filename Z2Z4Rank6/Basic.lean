import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Curves and point-group predicates

Definitions for Theorems 1.1 and 1.2 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

The point groups below are Mathlib's nonsingular Weierstrass point groups.
The rank lower bound means six points linearly independent over the integers.
-/

namespace Z2Z4Rank6

/-- The first polynomial in equation (1.1). -/
def a {R : Type*} [CommRing R] (m : R) : R :=
  7 * (m - 99) * (m + 1) * (m - 11) * (m + 9)

/-- The second polynomial in equation (1.1). -/
def b {R : Type*} [CommRing R] (m : R) : R :=
  -7 * (m + 99) * (m - 1) * (m + 11) * (m - 9)

/-- The Weierstrass equation `y² = x(x+a²)(x+b²)`. -/
def E {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := a ^ 2 + b ^ 2
  a₃ := 0
  a₄ := a ^ 2 * b ^ 2
  a₆ := 0

/-- The family `X`, evaluated at a parameter in the coefficient ring. -/
def X {R : Type*} [CommRing R] (m : R) : WeierstrassCurve R :=
  E (a m) (b m)

/-- The elliptic curve `E_C` printed in Theorem 1.2(a). -/
def EC : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 0
  a₄ := -137620
  a₆ := -10504000

/-- A rational point of the affine curve `C` in equation (1.3). -/
@[ext]
structure CPoint where
  m : ℚ
  u : ℚ
  v : ℚ
  u_sq : u ^ 2 = 5 * (3 * m ^ 2 + 242)
  v_sq : v ^ 2 = 5 * (2 * m ^ 2 + 243)

/-- The rational point group of a Weierstrass curve, with the usual point at infinity. -/
abbrev RationalPoints (W : WeierstrassCurve ℚ) := W.toAffine.Point

/-- The Weierstrass equation is an elliptic curve over the rationals. -/
abbrev GoodCurve (W : WeierstrassCurve ℚ) : Prop := W.IsElliptic

/-- The rational torsion subgroup is isomorphic to `Z/2 × Z/4`. -/
def TorsionExact (W : WeierstrassCurve ℚ) : Prop :=
  Nonempty (AddCommGroup.torsion (RationalPoints W) ≃+ (ZMod 2 × ZMod 4))

/-- The rational torsion subgroup contains a copy of `Z/2 × Z/4`. -/
def TorsionContains (W : WeierstrassCurve ℚ) : Prop :=
  ∃ f : (ZMod 2 × ZMod 4) →+ AddCommGroup.torsion (RationalPoints W),
    Function.Injective f

/-- The rational point group contains six integer-linearly independent points. -/
def RankAtLeastSix (W : WeierstrassCurve ℚ) : Prop :=
  ∃ P : Fin 6 → RationalPoints W, LinearIndependent ℤ P

/-- a rational elliptic curve has the torsion and rank required in Theorem 1.1. -/
def DesiredCurve (W : WeierstrassCurve ℚ) : Prop :=
  GoodCurve W ∧ TorsionExact W ∧ RankAtLeastSix W

/-- The usual `j` formula, extended to all Weierstrass equations. On elliptic
curves it equals Mathlib's `WeierstrassCurve.j`. -/
noncomputable def jValue (W : WeierstrassCurve ℚ) : ℚ :=
  W.Δ⁻¹ * W.c₄ ^ 3

/-- The extended formula is the `j`-invariant whenever the equation is elliptic. -/
theorem jValue_eq_j (W : WeierstrassCurve ℚ) [W.IsElliptic] : jValue W = W.j := by
  exact (WeierstrassCurve.j_eq W).symm

end Z2Z4Rank6
