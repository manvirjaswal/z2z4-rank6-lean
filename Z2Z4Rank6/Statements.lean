module

public import Z2Z4Rank6.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-!
# Statements of the main theorem

Statement definitions for Theorem 1.1 and Theorem 1.2(c) of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

Theorem 1.2(a) and (b) are stated in `FirstBaseGeometry.lean` and `RankSixExact.lean`.
-/

namespace Z2Z4Rank6

/-- The rational `j`-invariants of elliptic curves with exact torsion `Z/2 × Z/4`
and six integer-linearly independent rational points. -/
def desiredJInvariants : Set ℚ :=
  {j | ∃ W : WeierstrassCurve ℚ, DesiredCurve W ∧ jValue W = j}

/-- Theorem 1.1: infinitely many rational elliptic curves have torsion
isomorphic to `Z/2 × Z/4` and six integer-linearly independent rational points;
infinitely many distinct rational `j`-invariants occur among them.

The curves are represented by Weierstrass equations. The infinite set of
`j`-invariants guarantees infinitely many isomorphism classes, so this choice of
representation does not weaken the printed assertion. -/
def Theorem11 : Prop :=
  {W : WeierstrassCurve ℚ | DesiredCurve W}.Infinite ∧ desiredJInvariants.Infinite

/-- The displayed exceptional rational points of Theorem 1.2(c), with every sign
chosen independently. -/
def exceptionalPoints : Set CPoint :=
  {c | ((c.m = 1 ∨ c.m = -1) ∧ (c.u = 35 ∨ c.u = -35) ∧
      (c.v = 35 ∨ c.v = -35)) ∨
    ((c.m = 99 ∨ c.m = -99) ∧ (c.u = 385 ∨ c.u = -385) ∧
      (c.v = 315 ∨ c.v = -315))}

/-- Theorem 1.2(c): away from the sixteen displayed points, each fiber
is elliptic and its rational torsion contains `Z/2 × Z/4`; outside a finite set
of rational points of `C`, each fiber has exactly this torsion and six independent
rational points.

The second clause also says that these fibers are elliptic. This follows from
the first clause because the displayed exceptional set is finite; it makes
explicit what the printed phrase "the torsion subgroup ... and the rank" requires. -/
def Theorem12c : Prop :=
  (∀ c : CPoint, c ∉ exceptionalPoints →
    GoodCurve (X c.m) ∧ TorsionContains (X c.m)) ∧
  {c : CPoint | ¬DesiredCurve (X c.m)}.Finite

/-- The invariant set is exactly the image of the desired equations under `j`. -/
theorem desiredJInvariants_eq_image :
    desiredJInvariants = jValue '' {W : WeierstrassCurve ℚ | DesiredCurve W} := by
  ext j
  rfl

/-- Infinitely many distinct `j`-invariants supply the curve infinitude clause. -/
theorem infinite_curves_of_infinite_j (h : desiredJInvariants.Infinite) :
    {W : WeierstrassCurve ℚ | DesiredCurve W}.Infinite := by
  rw [desiredJInvariants_eq_image] at h
  exact h.of_image jValue

/-- To prove Theorem 1.1 it suffices to prove its distinct-`j` clause. -/
theorem theorem11_of_infinite_j (h : desiredJInvariants.Infinite) : Theorem11 :=
  ⟨infinite_curves_of_infinite_j h, h⟩

end Z2Z4Rank6
