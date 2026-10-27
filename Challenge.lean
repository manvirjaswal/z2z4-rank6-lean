module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Data.Set.Finite.Basic

/-!
# Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six

The statement of Theorem 1.1 of

  Manvir Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
  preprint, Zenodo, 2026, https://doi.org/10.5281/zenodo.23437117,

with the definitions it uses. This file imports only Mathlib: the Mathlib modules that the library
imports where these definitions are made, so that they elaborate to the same terms. `Solution.lean`
imports the proof, and Comparator checks that it proves exactly this statement using only the
standard axioms.

Theorem 1.1 says that infinitely many elliptic curves over `ℚ` have torsion subgroup isomorphic to
`ℤ/2ℤ × ℤ/4ℤ` and rank at least six, and that they have infinitely many distinct `j`-invariants, so
they fall into infinitely many isomorphism classes. A curve is given by a Weierstrass equation `W`
over `ℚ` with nonzero discriminant; its rational points form Mathlib's group `W.toAffine.Point`, and
rank at least six means six rational points that are linearly independent over `ℤ`.

The theorem takes four published theorems as hypotheses. Each is a proposition, defined below and
passed as an explicit argument; no axiom is added.

* `MazurTorsionTheorem`: the torsion subgroups of elliptic curves over `ℚ` are the fifteen groups of
  Mazur's theorem (Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977),
  Theorem (8)).
* `OddPrimeTorsionIntegrality`: on a Weierstrass equation with integer coefficients, an affine point
  of finite order has `x`-coordinate integral at every odd prime (Silverman, *The Arithmetic of
  Elliptic Curves*, 2nd ed., Theorem VII.3.4).
* `GoodReductionHomomorphisms`: at a prime of good reduction, reduction of points is a group
  homomorphism (Silverman, Proposition VII.2.1).
* `LocalEllipticTopology`: the points of an elliptic curve over `ℚ_p` form a compact topological
  group in which the inclusion of the affine solutions is an open embedding (Milne, *Elliptic
  Curves*, 2nd ed., II §4, proof of Theorem 4.1(a)).
-/

@[expose] public section

namespace Z2Z4Rank6

/-- The group `W(ℚ)` of rational points of a Weierstrass equation over `ℚ`: Mathlib's nonsingular
affine points together with the point at infinity, with the chord-and-tangent group law. -/
abbrev RationalPoints (W : WeierstrassCurve ℚ) := W.toAffine.Point

/-- `W` is an elliptic curve: its discriminant is a unit, that is, nonzero. -/
abbrev GoodCurve (W : WeierstrassCurve ℚ) : Prop := W.IsElliptic

-- The addition of `ZMod 2` below is taken from its ring structure `ZMod.commRing`, as in the
-- library, rather than from its field structure; the two additions are the same.
attribute [-instance] Nat.fact_prime_two in
/-- The torsion subgroup of `W(ℚ)` is isomorphic to `ℤ/2ℤ × ℤ/4ℤ`. -/
def TorsionExact (W : WeierstrassCurve ℚ) : Prop :=
  Nonempty (AddCommGroup.torsion (RationalPoints W) ≃+ (ZMod 2 × ZMod 4))

/-- `W(ℚ)` contains six points that are linearly independent over `ℤ`, so its rank is at least
six. -/
def RankAtLeastSix (W : WeierstrassCurve ℚ) : Prop :=
  ∃ P : Fin 6 → RationalPoints W, LinearIndependent ℤ P

/-- `W` is an elliptic curve over `ℚ` with torsion subgroup `ℤ/2ℤ × ℤ/4ℤ` and rank at least six. -/
def DesiredCurve (W : WeierstrassCurve ℚ) : Prop :=
  GoodCurve W ∧ TorsionExact W ∧ RankAtLeastSix W

/-- The `j`-invariant `c₄³/Δ`, written so that it is defined for every Weierstrass equation (it is
`0` when `Δ = 0`). On an elliptic curve it is Mathlib's `WeierstrassCurve.j`. -/
noncomputable def jValue (W : WeierstrassCurve ℚ) : ℚ :=
  W.Δ⁻¹ * W.c₄ ^ 3

/-- The rational number `q` is integral at `p`: `p` does not divide its reduced denominator. -/
def IntegralAt (p : ℕ) (q : ℚ) : Prop := (q.den : ZMod p) ≠ 0

/-- The reduction of `q` modulo the prime `p`, as numerator over denominator in `ZMod p`. It is the
residue class of `q` when `q` is integral at `p`. -/
def residue (p : ℕ) [Fact p.Prime] (q : ℚ) : ZMod p :=
  (q.num : ZMod p) / (q.den : ZMod p)

/-- The five coefficients of `W` are integral at `p`. -/
def IntegralModelAt (p : ℕ) (W : WeierstrassCurve ℚ) : Prop :=
  IntegralAt p W.a₁ ∧ IntegralAt p W.a₂ ∧ IntegralAt p W.a₃ ∧
    IntegralAt p W.a₄ ∧ IntegralAt p W.a₆

/-- The reduction of `W` modulo the prime `p`, coefficient by coefficient. It is used only when the
coefficients are integral at `p`. -/
def reducedModel (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ) : WeierstrassCurve (ZMod p) where
  a₁ := residue p W.a₁
  a₂ := residue p W.a₂
  a₃ := residue p W.a₃
  a₄ := residue p W.a₄
  a₆ := residue p W.a₆

/-- There is a group homomorphism from `W(ℚ)` to the points of the reduction of `W` modulo `p` that
sends every affine point `(x, y)` with `x` and `y` integral at `p` to the point
`(x mod p, y mod p)`. -/
def GoodReductionAt (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ) : Prop :=
  ∃ red : W.toAffine.Point →+ (reducedModel p W).toAffine.Point,
    ∀ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
      IntegralAt p x → IntegralAt p y →
      ∃ hred : (reducedModel p W).toAffine.Nonsingular (residue p x) (residue p y),
        red (.some x y h) = .some (residue p x) (residue p y) hred

/-- Reduction at a prime of good reduction is a homomorphism (Silverman, *The Arithmetic of Elliptic
Curves*, 2nd ed., Proposition VII.2.1): for every prime `p` and every elliptic curve `W` over `ℚ`
whose coefficients are integral at `p` and whose reduction modulo `p` is elliptic,
`GoodReductionAt p W` holds. -/
def GoodReductionHomomorphisms : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ),
    W.IsElliptic → IntegralModelAt p W → (reducedModel p W).IsElliptic →
      GoodReductionAt p W

/-- `W` has integer coefficients (it need not be a minimal model). -/
def IntegralWeierstrass (W : WeierstrassCurve ℚ) : Prop :=
  ∃ W₀ : WeierstrassCurve ℤ, W₀.map (Int.castRingHom ℚ) = W

/-- Integrality of torsion points at odd primes (Silverman, *The Arithmetic of Elliptic Curves*,
2nd ed., Theorem VII.3.4, over `ℚ_p` with `p` odd): if `W` is an elliptic curve over `ℚ` with
integer coefficients, `p` is an odd prime and `(x, y)` is an affine rational point of finite order,
then `p` does not divide the denominator of `x`. -/
def OddPrimeTorsionIntegrality : Prop :=
  ∀ (W : WeierstrassCurve ℚ), W.IsElliptic → IntegralWeierstrass W →
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x y h) → ¬ p ∣ x.den

/-- `G` is one of the fifteen groups of Mazur's theorem: `ℤ/nℤ` with `1 ≤ n ≤ 10` or `n = 12`, or
`ℤ/2ℤ × ℤ/2nℤ` with `1 ≤ n ≤ 4`. -/
def IsInMazurClass (G : Type*) [AddCommGroup G] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ (n ≤ 10 ∨ n = 12) ∧ Nonempty (G ≃+ ZMod n)) ∨
  ∃ n : ℕ, 1 ≤ n ∧ n ≤ 4 ∧ Nonempty (G ≃+ (ZMod 2 × ZMod (2 * n)))

/-- Mazur's theorem (Mazur, *Modular curves and the Eisenstein ideal*, Publ. Math. IHÉS 47 (1977),
Theorem (8)): the torsion subgroup of the rational points of every elliptic curve over `ℚ` is one of
the fifteen groups of `IsInMazurClass`. -/
def MazurTorsionTheorem : Prop :=
  ∀ W : WeierstrassCurve ℚ, GoodCurve W →
    IsInMazurClass (AddCommGroup.torsion (RationalPoints W))

open Topology

/-- The affine solutions `(x, y) ∈ K × K` of the equation `W`, with the subspace topology of `K × K`
when `K` is a topological field. -/
abbrev AffineEquationPoints {K : Type*} [Field K] (W : WeierstrassCurve K) :=
  {xy : K × K // W.toAffine.Equation xy.1 xy.2}

/-- The inclusion of the affine solutions into the points of an elliptic curve. -/
def affinePointEmbedding {K : Type*} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (xy : AffineEquationPoints W) : W.toAffine.Point :=
  WeierstrassCurve.Affine.Point.mk xy.property

/-- The points of the elliptic curve `W` over `ℚ_p` carry a topology in which they form a compact
topological group and the inclusion of the affine solutions, with the topology of `ℚ_p × ℚ_p`, is an
open embedding. -/
def LocalEllipticTopologyAt {p : ℕ} [Fact p.Prime]
    (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] : Prop := by
  classical
  exact ∃ T : TopologicalSpace W.toAffine.Point,
    letI := T
    CompactSpace W.toAffine.Point ∧ IsTopologicalAddGroup W.toAffine.Point ∧
      IsOpenEmbedding (affinePointEmbedding W)

/-- The topology of elliptic curves over `ℚ_p` (Milne, *Elliptic Curves*, 2nd ed., II §4, proof of
Theorem 4.1(a); Fisher, *Elliptic Curves*, Cambridge Part III lecture notes by L. Tomczak, 2023,
proof of Lemma 9.8): `LocalEllipticTopologyAt` holds for every prime `p` and every elliptic curve
`W` over `ℚ_p`. -/
def LocalEllipticTopology : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) (hW : W.IsElliptic),
    letI := hW
    LocalEllipticTopologyAt W

/-- The `j`-invariants of the elliptic curves over `ℚ` with torsion subgroup `ℤ/2ℤ × ℤ/4ℤ` and rank
at least six. -/
def desiredJInvariants : Set ℚ :=
  {j | ∃ W : WeierstrassCurve ℚ, DesiredCurve W ∧ jValue W = j}

/-- The assertion of Theorem 1.1: infinitely many Weierstrass equations over `ℚ` are elliptic curves
with torsion subgroup `ℤ/2ℤ × ℤ/4ℤ` and rank at least six, and their `j`-invariants are infinitely
many, so they fall into infinitely many isomorphism classes. -/
def Theorem11 : Prop :=
  {W : WeierstrassCurve ℚ | DesiredCurve W}.Infinite ∧ desiredJInvariants.Infinite

/-- **Theorem 1.1.** Infinitely many elliptic curves over `ℚ` have torsion subgroup `ℤ/2ℤ × ℤ/4ℤ`
and rank at least six, with infinitely many distinct `j`-invariants. The four hypotheses are the
published theorems described above. -/
theorem theorem_1_1
    (hMazur : MazurTorsionTheorem)
    (hSilvermanVII34 : OddPrimeTorsionIntegrality)
    (hReduction : GoodReductionHomomorphisms)
    (hLocal : LocalEllipticTopology) : Theorem11 := by
  sorry

end Z2Z4Rank6
