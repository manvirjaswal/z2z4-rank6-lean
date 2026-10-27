import Z2Z4Rank6.Basic
import Z2Z4Rank6.Residue

/-!
# The published good-reduction homomorphism theorem

It is stated for every prime and elliptic curve.

References:
* T. Fisher, *Elliptic Curves*, Cambridge Part III, Lent 2023, lecture notes
  taken by L. Tomczak, Proposition 9.5, p. 28; affine reduction is defined on
  p. 27. At good reduction its domain E₀(K) is E(K). A unit discriminant makes
  the given integral equation minimal.
  https://math.berkeley.edu/~ltomczak/notes/Lent2023/EC_Notes.pdf
* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021,
  Chapter II, Section 4, pp. 62–63, Theorem 4.1(b). The opening discussion
  explains that minimality is not needed there.
  https://jmilne.org/math/Books/EC2.pdf

The rational statement below is the restriction of the local-field theorem
along Q → Q_p. Integral rational coordinates reduce by their numerator and
unit denominator, as encoded in `residue`.
-/

namespace Z2Z4Rank6

/-- All five rational coefficients of W are integral at p. -/
def IntegralModelAt (p : ℕ) (W : WeierstrassCurve ℚ) : Prop :=
  IntegralAt p W.a₁ ∧ IntegralAt p W.a₂ ∧ IntegralAt p W.a₃ ∧
    IntegralAt p W.a₄ ∧ IntegralAt p W.a₆

/-- Coefficient reduction of a rational Weierstrass equation. It is used as a
model only when its five coefficients are integral at p. -/
def reducedModel (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ) : WeierstrassCurve (ZMod p) where
  a₁ := residue p W.a₁
  a₂ := residue p W.a₂
  a₃ := residue p W.a₃
  a₄ := residue p W.a₄
  a₆ := residue p W.a₆

/-- At good reduction there is an additive reduction homomorphism on
all rational points; on integral affine coordinates it reduces each coordinate.
The target nonsingularity proof is included so this refers to the
Mathlib elliptic point group. Surjectivity is unnecessary for the application. -/
def GoodReductionAt (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ) : Prop :=
  ∃ red : W.toAffine.Point →+ (reducedModel p W).toAffine.Point,
    ∀ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
      IntegralAt p x → IntegralAt p y →
      ∃ hred : (reducedModel p W).toAffine.Nonsingular (residue p x) (residue p y),
        red (.some x y h) = .some (residue p x) (residue p y) hred

/-- The published good-reduction homomorphism theorem is available for
every rational elliptic curve, every prime, and every model with integral
coefficients and nonsingular reduction. -/
def GoodReductionHomomorphisms : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ),
    W.IsElliptic → IntegralModelAt p W → (reducedModel p W).IsElliptic →
      GoodReductionAt p W

end Z2Z4Rank6
