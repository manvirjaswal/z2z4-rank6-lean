module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Local quartic certificates for the rank bound on E_C

The printed E_C of Lemma 4.1(b), in M. Jaswal, *Infinitely many elliptic
curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117, translates to the split model
`y²=x(x²+1213x+352836)`. Its two-isogenous curve has coefficients
`-2426,60025`.

The local tests use the homogeneous quartics in Cremona, *Algorithms for
Modular Elliptic Curves*, 2nd ed. (1997), Section 3.6, Method 1. The rank
bound in ECExactRank uses the complete-descent image bound in ECDescentImage;
this module proves the local obstructions.
-/

namespace Z2Z4Rank6

/-- A homogeneous quartic used in two-isogeny descent. -/
def descentQuartic {R : Type*} [CommRing R] (d A e u v : R) : R :=
  d*u^4 + A*u^2*v^2 + e*v^4

/-- A projectively primitive residue solution of one quartic. -/
def PrimitiveQuarticSolubleMod (p : ℕ) (d A e : ℤ) : Prop :=
  ∃ u v n : ZMod p, (u ≠ 0 ∨ v ≠ 0) ∧
    n^2 = descentQuartic (d : ZMod p) (A : ZMod p) (e : ZMod p) u v

instance (p : ℕ) [NeZero p] (d A e : ℤ) :
    Decidable (PrimitiveQuarticSolubleMod p d A e) :=
  inferInstanceAs (Decidable (∃ u v n : ZMod p, (u ≠ 0 ∨ v ≠ 0) ∧
    n^2 = descentQuartic (d : ZMod p) (A : ZMod p) (e : ZMod p) u v))

theorem ec_mod5_obstruction :
    ∀ d ∈ ([-33,-22,-3,-2,2,3,22,33] : List ℤ),
      ¬PrimitiveQuarticSolubleMod 5 d 1213 (352836/d) := by
  decide +kernel

theorem ecIsogenous_mod3_obstruction :
    ∀ d ∈ ([5,35] : List ℤ),
      ¬PrimitiveQuarticSolubleMod 3 d (-2426) (60025/d) := by
  decide +kernel

theorem ecIsogenous_mod11_obstruction :
    ¬PrimitiveQuarticSolubleMod 11 7 (-2426) 8575 := by
  decide +kernel

/-- A negative representative has no real point on any projective chart of
the isogenous homogeneous quartic. -/
theorem ecIsogenous_real_obstruction (d e u v n : ℝ) (hd : d < 0) (he : e < 0)
    (hnonzero : u ≠ 0 ∨ v ≠ 0) :
    n^2 ≠ descentQuartic d (-2426) e u v := by
  intro h
  have hu4 : 0 ≤ u^4 := by positivity
  have hv4 : 0 ≤ v^4 := by positivity
  have huv : 0 ≤ u^2*v^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rcases hnonzero with hu | hv
  · have hp : 0 < u^4 := by
      simpa only [←pow_mul] using pow_pos (sq_pos_of_ne_zero hu) 2
    have hn : d*u^4 < 0 := mul_neg_of_neg_of_pos hd hp
    unfold descentQuartic at h
    nlinarith [sq_nonneg n, mul_nonpos_of_nonpos_of_nonneg he.le hv4]
  · have hp : 0 < v^4 := by
      simpa only [←pow_mul] using pow_pos (sq_pos_of_ne_zero hv) 2
    have hn : e*v^4 < 0 := mul_neg_of_neg_of_pos he hp
    unfold descentQuartic at h
    nlinarith [sq_nonneg n, mul_nonpos_of_nonpos_of_nonneg hd.le hu4]

end Z2Z4Rank6
