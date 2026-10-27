import Z2Z4Rank6.JInvariant
import Z2Z4Rank6.Twists
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Degrees and bounds for the j-invariant fibers

The polynomial degrees and the bound of 192 in the proof of Theorem 1.1 of
Manvir Jaswal, "Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and
rank at least six", DOI: 10.5281/zenodo.23437117.

The printed numerator and denominator are checked to be coprime, and their
degrees agree with the reduced numerator and denominator of the
rational function. The fiber bound also follows directly from the polynomial
equation and the two square-root signs on C.
-/

namespace Z2Z4Rank6

open Polynomial Set GCDMonoid

/-- The printed numerator has degree 48 in m. -/
theorem jNumerator_natDegree : jNumerator.natDegree = 48 := by
  unfold jNumerator a b
  compute_degree!

/-- The printed denominator has degree 46 in m. -/
theorem jDenominator_natDegree : jDenominator.natDegree = 46 := by
  have hdiff : (a (Polynomial.X : ℚ[X])) ^ 2 - (b Polynomial.X) ^ 2 =
      (14 * (Polynomial.X ^ 4 - 2 * Polynomial.X ^ 2 + 9801)) *
        (-1400 * Polynomial.X * (Polynomial.X ^ 2 - 99)) := by
    rw [show (a (Polynomial.X : ℚ[X])) ^ 2 - (b Polynomial.X) ^ 2 =
      (a Polynomial.X - b Polynomial.X) * (a Polynomial.X + b Polynomial.X) by ring,
      a_sub_b, a_add_b]
  unfold jDenominator
  rw [hdiff]
  unfold a b
  compute_degree!

/-- Every equation for a fixed j-value still has degree 48, since its second
term has degree at most 46. -/
theorem j_fiber_polynomial_natDegree (j : ℚ) :
    (jNumerator - Polynomial.C j * jDenominator).natDegree = 48 := by
  have hdeg : (Polynomial.C j * jDenominator).natDegree < jNumerator.natDegree := by
    have hle := Polynomial.natDegree_mul_le (p := Polynomial.C j) (q := jDenominator)
    simp only [Polynomial.natDegree_C, zero_add, jDenominator_natDegree] at hle
    rw [jNumerator_natDegree]
    omega
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg, jNumerator_natDegree]

/-- There are at most 48 rational parameters satisfying one j-value equation. -/
theorem ncard_j_parameter_roots_le (j : ℚ) :
    {m : ℚ | (jNumerator - Polynomial.C j * jDenominator).eval m = 0}.ncard ≤ 48 := by
  have heq : {m : ℚ | (jNumerator - Polynomial.C j * jDenominator).eval m = 0} =
      (jNumerator - Polynomial.C j * jDenominator).rootSet ℚ := by
    ext m
    simp [Polynomial.mem_rootSet_of_ne (j_fiber_polynomial_ne_zero j),
      Polynomial.aeval_def]
  rw [heq]
  exact (Polynomial.ncard_rootSet_le _ ℚ).trans (le_of_eq (j_fiber_polynomial_natDegree j))

private theorem rational_eq_of_sq_eq_and_same_sign (r s : ℚ)
    (hsq : r ^ 2 = s ^ 2) (hsign : decide (0 ≤ r) = decide (0 ≤ s)) : r = s := by
  have hiff : (0 ≤ r) ↔ (0 ≤ s) := decide_eq_decide.mp hsign
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · by_cases hr : 0 ≤ r
    · have hs := hiff.mp hr
      linarith
    · have hs : ¬0 ≤ s := mt hiff.mpr hr
      linarith

/-- A smooth fiber with j-value j satisfies the corresponding parameter equation. -/
theorem j_parameter_root_of_fiber (j : ℚ) (c : CPoint)
    (hc : GoodCurve (X c.m) ∧ jValue (X c.m) = j) :
    (jNumerator - Polynomial.C j * jDenominator).eval c.m = 0 := by
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  have he : jNumerator.eval c.m / jDenominator.eval c.m = j :=
    (jValue_X_eq c.m hc.1).symm.trans hc.2
  exact sub_eq_zero.mpr ((div_eq_iff (jDenominator_ne_zero c.m hc.1)).mp he)

/-- At most 192 rational points of C give a smooth fiber of any specified j-value.
For each of at most 48 parameters, the two signs of u and v give at most four points. -/
theorem ncard_j_CPoint_fiber_le (j : ℚ) :
    {c : CPoint | GoodCurve (X c.m) ∧ jValue (X c.m) = j}.ncard ≤ 192 := by
  classical
  let S : Set CPoint := {c | GoodCurve (X c.m) ∧ jValue (X c.m) = j}
  let T : Set ℚ := {m | (jNumerator - Polynomial.C j * jDenominator).eval m = 0}
  have : Finite T := (finite_j_parameter_roots j).to_subtype
  let f : S → T × (Bool × Bool) := fun c =>
    (⟨c.val.m, j_parameter_root_of_fiber j c.val c.property⟩,
      decide (0 ≤ c.val.u), decide (0 ≤ c.val.v))
  have hf : Function.Injective f := by
    intro c d he
    have hm : c.val.m = d.val.m := congrArg (fun z : T × (Bool × Bool) => z.1.val) he
    have hu : decide (0 ≤ c.val.u) = decide (0 ≤ d.val.u) :=
      congrArg (fun z : T × (Bool × Bool) => z.2.1) he
    have hv : decide (0 ≤ c.val.v) = decide (0 ≤ d.val.v) :=
      congrArg (fun z : T × (Bool × Bool) => z.2.2) he
    apply Subtype.ext
    apply CPoint.ext hm
    · apply rational_eq_of_sq_eq_and_same_sign _ _ _ hu
      rw [c.val.u_sq, d.val.u_sq, hm]
    · apply rational_eq_of_sq_eq_and_same_sign _ _ _ hv
      rw [c.val.v_sq, d.val.v_sq, hm]
  have hc := Nat.card_le_card_of_injective f hf
  have hbool : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card, Fintype.card_bool]
  simp only [Nat.card_prod, hbool] at hc
  have ht : T.ncard ≤ 48 := ncard_j_parameter_roots_le j
  change Nat.card S ≤ 192
  change Nat.card T ≤ 48 at ht
  omega

/-- A short Bézout certificate verifies that the printed a and b are coprime.
The coefficients were computed by `PARI/GP`; the identity is
checked here by ring normalization. -/
theorem isCoprime_a_b_poly :
    IsCoprime (a (Polynomial.X : ℚ[X])) (b Polynomial.X) := by
  let s : ℚ[X] := -97 * Polynomial.X ^ 3 - 9700 * Polynomial.X ^ 2 +
    9995 * Polynomial.X + 1940400
  let t : ℚ[X] := -97 * Polynomial.X ^ 3 + 9700 * Polynomial.X ^ 2 +
    9995 * Polynomial.X - 1940400
  have h : s * a Polynomial.X + t * b Polynomial.X = (266250045600 : ℚ[X]) := by
    dsimp [s, t, a, b]
    ring
  refine ⟨Polynomial.C ((266250045600 : ℚ)⁻¹) * s,
    Polynomial.C ((266250045600 : ℚ)⁻¹) * t, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h]
  change Polynomial.C ((266250045600 : ℚ)⁻¹) *
    Polynomial.C (266250045600 : ℚ) = Polynomial.C (1 : ℚ)
  rw [← Polynomial.C_mul]
  norm_num

private theorem coprime_quartic_parts {R : Type*} [CommRing R] (a b : R)
    (hab : IsCoprime a b) :
    IsCoprime (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4)
      (a ^ 4 * b ^ 4 * (a ^ 2 - b ^ 2) ^ 2) := by
  have ha : IsCoprime (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4) a := by
    convert (hab.symm.pow_left (m := 4)).add_mul_right_left (a * (a ^ 2 - b ^ 2)) using 1; ring
  have hb : IsCoprime (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4) b := by
    convert (hab.pow_left (m := 4)).add_mul_right_left (b * (b ^ 2 - a ^ 2)) using 1; ring
  have hbD : IsCoprime b (a ^ 2 - b ^ 2) := by
    convert (hab.symm.pow_right (n := 2)).add_mul_right_right (-b) using 1; ring
  have hD : IsCoprime (a ^ 4 - a ^ 2 * b ^ 2 + b ^ 4) (a ^ 2 - b ^ 2) := by
    convert (hbD.pow_left (m := 4)).add_mul_right_left (a ^ 2) using 1; ring
  exact (ha.pow_right.mul_right hb.pow_right).mul_right hD.pow_right

/-- The printed numerator and denominator have no common polynomial factor. -/
theorem isCoprime_jNumerator_jDenominator : IsCoprime jNumerator jDenominator := by
  have h256 : IsUnit (256 : ℚ[X]) := by
    change IsUnit (Polynomial.C (256 : ℚ))
    exact Polynomial.isUnit_C.mpr (by norm_num)
  unfold jNumerator jDenominator
  apply (isCoprime_mul_unit_left_left h256 _ _).2
  exact (coprime_quartic_parts _ _ isCoprime_a_b_poly).pow_left

/-- The printed j-invariant as a rational function in m. -/
noncomputable def jRationalFunction : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) jNumerator /
    algebraMap ℚ[X] (RatFunc ℚ) jDenominator

private theorem jDenominator_poly_ne_zero : jDenominator ≠ 0 := by
  intro h
  have hd := jDenominator_natDegree
  simp only [h, Polynomial.natDegree_zero] at hd
  contradiction

section ClassicalGCD

-- RatFunc's generic normalized GCD instance uses classical equality on its
-- coefficient field; fixing that same instance avoids an implementation-only
-- mismatch with the computable equality instance for the rational numbers.
noncomputable local instance : DecidableEq ℚ := Classical.decEq ℚ

private theorem j_parts_gcd_eq_one : gcd jNumerator jDenominator = 1 := by
  have hu : IsUnit (gcd jNumerator jDenominator) :=
    isCoprime_jNumerator_jDenominator.isUnit_of_dvd'
      (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hn := normalize_eq_one.mpr hu
  rwa [normalize_gcd] at hn

/-- The reduced numerator of the rational function still has degree 48. -/
theorem jRationalFunction_num_natDegree : jRationalFunction.num.natDegree = 48 := by
  classical
  unfold jRationalFunction
  rw [RatFunc.num_div, j_parts_gcd_eq_one, EuclideanDomain.div_one, EuclideanDomain.div_one,
    Polynomial.natDegree_C_mul (inv_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr jDenominator_poly_ne_zero))]
  exact jNumerator_natDegree

/-- The reduced denominator of the rational function has degree 46. -/
theorem jRationalFunction_denom_natDegree : jRationalFunction.denom.natDegree = 46 := by
  classical
  unfold jRationalFunction
  rw [RatFunc.denom_div _ jDenominator_poly_ne_zero, j_parts_gcd_eq_one, EuclideanDomain.div_one,
    Polynomial.natDegree_C_mul (inv_ne_zero
      (Polynomial.leadingCoeff_ne_zero.mpr jDenominator_poly_ne_zero))]
  exact jDenominator_natDegree

/-- The rational-map degree, the maximum of reduced numerator and denominator
degrees, is exactly 48 as printed. -/
theorem jRationalFunction_map_degree :
    max jRationalFunction.num.natDegree jRationalFunction.denom.natDegree = 48 := by
  rw [jRationalFunction_num_natDegree, jRationalFunction_denom_natDegree]
  decide

/-- The rational function is nonconstant. -/
theorem jRationalFunction_ne_constant (q : ℚ) :
    jRationalFunction ≠ algebraMap ℚ (RatFunc ℚ) q := by
  intro h
  have hd := jRationalFunction_denom_natDegree
  have he : jRationalFunction = algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C q) := by
    rw [h]
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) q
  rw [he, RatFunc.denom_algebraMap, Polynomial.natDegree_one] at hd
  contradiction

end ClassicalGCD

end Z2Z4Rank6
