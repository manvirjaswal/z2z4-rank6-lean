import Z2Z4Rank6.Basic
import Mathlib.Tactic

/-!
# Three sections of the Dujella–Peral family

The coordinates and factorizations of Lemma 2.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. All identities hold over any commutative
ring. The signs of the ordinates are the signs printed in the paper.
-/

namespace Z2Z4Rank6

variable {R : Type*} [CommRing R]

def p1x (m : R) : R :=
  -49 * (m - 1)^2 * (m - 11)^2 * (m + 9)^2 * (m + 99)^2

def p1y (m : R) : R :=
  -19208 * m * (m^2 - 99) * (m - 1)^2 * (m - 11)^2 * (m + 9)^2 * (m + 99)^2

def p2x (m : R) : R :=
  49 * (m - 99) * (m - 1) * (m + 1) * (m + 99) * (m - 9)^2 * (m + 11)^2

def p2y (m : R) : R :=
  -686 * (m - 99) * (m - 1) * (m + 1) * (m + 99) * (m^2 - 99) *
    (m^2 + 99) * (m - 9)^2 * (m + 11)^2

def p3x (m : R) : R :=
  -49 * (m - 11) * (m - 9) * (m + 1) * (m + 99) * (m + 9)^2 * (m + 11)^2

def p3y (m : R) : R :=
  27440 * m * (m - 6) * (m - 9) * (m - 11) * (m + 1) * (m + 99) *
    (2*m - 33) * (m + 9)^2 * (m + 11)^2

/-- The first displayed factorization for P₁ in Lemma 2.2. -/
theorem p1x_add_a_sq (m : R) :
    p1x m + (a m)^2 = -19208*m*(m^2-99)*(m-11)^2*(m+9)^2 := by
  unfold p1x a
  ring

/-- The second displayed factorization for P₁ in Lemma 2.2. -/
theorem p1x_add_b_sq (m : R) :
    p1x m + (b m)^2 = 392*m*(m^2-99)*(m-1)^2*(m+99)^2 := by
  unfold p1x b
  ring

theorem p2x_add_a_sq (m : R) :
    p2x m + (a m)^2 = 98*(m-99)*(m+1)*(m^2-99)*(m^2+99)^2 := by
  unfold p2x a
  ring

theorem p2x_add_b_sq (m : R) :
    p2x m + (b m)^2 = 98*(m-1)*(m+99)*(m^2-99)*(m-9)^2*(m+11)^2 := by
  unfold p2x b
  ring

theorem p3x_add_a_sq (m : R) :
    p3x m + (a m)^2 = -3920*m*(m-11)*(m+1)*(m+9)^2*(2*m-33)^2 := by
  unfold p3x a
  ring

theorem p3x_add_b_sq (m : R) :
    p3x m + (b m)^2 = 3920*m*(m-9)*(m+99)*(m-6)^2*(m+11)^2 := by
  unfold p3x b
  ring

/-- P₁ satisfies the equation of X, with the ordinate printed in Lemma 2.2. -/
theorem p1_equation (m : R) :
    (p1y m)^2 = p1x m * (p1x m + (a m)^2) * (p1x m + (b m)^2) := by
  rw [p1x_add_a_sq, p1x_add_b_sq]
  unfold p1x p1y
  ring

/-- P₂ satisfies the equation of X, with the ordinate printed in Lemma 2.2. -/
theorem p2_equation (m : R) :
    (p2y m)^2 = p2x m * (p2x m + (a m)^2) * (p2x m + (b m)^2) := by
  rw [p2x_add_a_sq, p2x_add_b_sq]
  unfold p2x p2y
  ring

/-- P₃ satisfies the equation of X, with the ordinate printed in Lemma 2.2. -/
theorem p3_equation (m : R) :
    (p3y m)^2 = p3x m * (p3x m + (a m)^2) * (p3x m + (b m)^2) := by
  rw [p3x_add_a_sq, p3x_add_b_sq]
  unfold p3x p3y
  ring

/-- The factored equation used in the paper is Mathlib's Weierstrass equation. -/
theorem E_equation_iff_factored (a b x y : R) :
    (E a b).toAffine.Equation x y ↔ y^2=x*(x+a^2)*(x+b^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [E, zero_mul, add_zero]
  ring_nf

theorem p1_affine_equation (m : R) : (X m).toAffine.Equation (p1x m) (p1y m) := by
  exact (E_equation_iff_factored _ _ _ _).2 (p1_equation m)

theorem p2_affine_equation (m : R) : (X m).toAffine.Equation (p2x m) (p2y m) := by
  exact (E_equation_iff_factored _ _ _ _).2 (p2_equation m)

theorem p3_affine_equation (m : R) : (X m).toAffine.Equation (p3x m) (p3y m) := by
  exact (E_equation_iff_factored _ _ _ _).2 (p3_equation m)

/-- P₁ as a point of the Mathlib elliptic-curve group. -/
def point1 (m : R) [Nontrivial R] [(X m).IsElliptic] : (X m).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (p1_affine_equation m)

/-- P₂ as a point of the Mathlib elliptic-curve group. -/
def point2 (m : R) [Nontrivial R] [(X m).IsElliptic] : (X m).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (p2_affine_equation m)

/-- P₃ as a point of the Mathlib elliptic-curve group. -/
def point3 (m : R) [Nontrivial R] [(X m).IsElliptic] : (X m).toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk (p3_affine_equation m)

end Z2Z4Rank6
