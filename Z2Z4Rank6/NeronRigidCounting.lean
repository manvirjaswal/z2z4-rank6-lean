import Z2Z4Rank6.RigidRationalPlace
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card

/-!
# Néron's counting theorem in normalized rational-place form

Source: A. Néron, Problèmes arithmétique et géométriques rattachés à la notion
de rang d'une courbe algébrique dans un corps, Bull. Soc. Math. France 80 (1952),
101–166, DOI 10.24033/bsmf.1427, Chapter III, Theorem 4 and Lemma 20, p. 151,
Corollary 2, pp. 152–153. It counts rational points on a genus-one curve by
the rational height of a nonconstant function, with logarithmic exponent
half the Mordell–Weil rank.

This function-field form is a direct corollary, not a numbered statement in the source. A rational
algebra equivalence to Mathlib's elliptic
function field supplies the genus-one model. The rational/RatFunc scalar
tower and finite extension fix a nonconstant parameter. Function-field/model
identification uses Stacks 53.2.6/8, tag 0BXX; rational places are the points of
the proper smooth model. Its completion with fixed rational coefficients
and uniformizer is Stacks 10.160.10, tag 0323. The identity t=c+T gives exactly
one normalized place at each unramified rational point where t is finite.
Branch and pole points form a finite excluded set. Removing that finite set
preserves the positive-rank logarithmic exponent.
-/

namespace Z2Z4Rank6

universe u
noncomputable section

/-- Reduced rational height: maximum of the absolute numerator and positive
denominator. This is an integer, including at zero. -/
def rationalParameterHeight (q : ℚ) : ℕ := max q.num.natAbs q.den

/-- All normalized rational places with bounded parameter height. -/
def rigidPlaceHeightSet (K : Type u) [Field K] [Algebra ℚ K]
    [Algebra (RatFunc ℚ) K] (H : ℕ) : Set (RigidRationalPlace K) :=
  {v | rationalParameterHeight v.parameter≤H}

/-- Cardinality of the bounded-place set. Its finiteness is a separate conclusion of the theorem
below. -/
def rigidPlaceCount (K : Type u) [Field K] [Algebra ℚ K]
    [Algebra (RatFunc ℚ) K] (H : ℕ) : ℕ := (rigidPlaceHeightSet K H).ncard

/-- Exact meaning of N(H)=(log H)^(a+o(1)), along natural height bounds.
The behavior at the finitely many small bounds does not affect this limit. -/
def HasLogarithmicCountingExponent (N : ℕ→ℕ) (a : ℝ) : Prop :=
  Filter.Tendsto (fun H : ℕ => Real.log (N H : ℝ)/Real.log (Real.log (H : ℝ)))
    Filter.atTop (nhds a)

/-- Every finite extension of the rational function field
which is rationally isomorphic to a rational elliptic function
field of positive rank r has finite bounded sets of normalized rational
places, and its counting function has logarithmic exponent r/2.
This is the generic normalized-place consequence of Néron's theorem. -/
def NeronRigidCountingTheorem : Prop :=
  ∀ (K : Type u) [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]
    [IsScalarTower ℚ (RatFunc ℚ) K] [FiniteDimensional (RatFunc ℚ) K]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (_ : K≃ₐ[ℚ]E.toAffine.FunctionField) (r : ℕ),
    0<r → Module.rank ℤ E.toAffine.Point=(r : Cardinal) →
    (∀ H : ℕ,(rigidPlaceHeightSet K H).Finite) ∧
      HasLogarithmicCountingExponent (rigidPlaceCount K) ((r : ℝ)/2)

/-- Apply the published input. -/
theorem rigid_place_counting (hN : NeronRigidCountingTheorem.{u})
    (K : Type u) [Field K] [Algebra ℚ K] [Algebra (RatFunc ℚ) K]
    [IsScalarTower ℚ (RatFunc ℚ) K] [FiniteDimensional (RatFunc ℚ) K]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (e : K≃ₐ[ℚ]E.toAffine.FunctionField) (r : ℕ) (hr : 0<r)
    (hRank : Module.rank ℤ E.toAffine.Point=(r : Cardinal)) :
    (∀ H : ℕ,(rigidPlaceHeightSet K H).Finite) ∧
      HasLogarithmicCountingExponent (rigidPlaceCount K) ((r : ℝ)/2) :=
  hN K E e r hr hRank

end
end Z2Z4Rank6
