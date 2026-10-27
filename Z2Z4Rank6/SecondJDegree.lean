import Z2Z4Rank6.SecondJInvariant
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Set.Card

/-!
# Degree twelve and the bound of 96 for the second family

The polynomial and reduced rational-function degrees in Theorem 8.1(c) of
Jaswal, DOI 10.5281/zenodo.23437117. At most 12 values of W give a fixed j,
and the three rational square-root signs give at most 8 points above W.
-/

namespace Z2Z4Rank6.SecondFamily
open Polynomial Set GCDMonoid
noncomputable section

theorem jNumerator_natDegree : jNumerator.natDegree=12 := by
  unfold jNumerator uPolynomial vPolynomial lambda
  compute_degree!
  norm_num [Polynomial.coeff_one]

theorem polynomial_discriminant_factor :
    uPolynomial^2-4*vPolynomial^2=
      16*(1+C (lambda:ℚ))^2*Polynomial.X*(Polynomial.X+C (lambda:ℚ))^2 := by
  unfold uPolynomial vPolynomial
  simp only [map_pow]
  ring

theorem jDenominator_natDegree : jDenominator.natDegree=11 := by
  unfold jDenominator
  rw [polynomial_discriminant_factor]
  unfold vPolynomial lambda
  compute_degree!
  norm_num [Polynomial.coeff_one]

theorem j_fiber_polynomial_natDegree (j : ℚ) :
    (jNumerator-C j*jDenominator).natDegree=12 := by
  have hdeg : (C j*jDenominator).natDegree<jNumerator.natDegree := by
    have h := Polynomial.natDegree_mul_le (p:=C j) (q:=jDenominator)
    simp only [natDegree_C,zero_add,jDenominator_natDegree] at h
    rw [jNumerator_natDegree]
    omega
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg,jNumerator_natDegree]

theorem ncard_j_parameter_roots_le (j : ℚ) :
    {w : ℚ | (jNumerator-C j*jDenominator).eval w=0}.ncard≤12 := by
  have he : {w : ℚ | (jNumerator-C j*jDenominator).eval w=0}=
      (jNumerator-C j*jDenominator).rootSet ℚ := by
    ext w
    simp [Polynomial.mem_rootSet_of_ne (j_fiber_polynomial_ne_zero j),Polynomial.aeval_def]
  rw [he]
  exact (Polynomial.ncard_rootSet_le _ ℚ).trans (le_of_eq (j_fiber_polynomial_natDegree j))

private theorem rational_eq_of_sq_eq_and_sign (r s : ℚ) (hsq : r^2=s^2)
    (hsign : decide (0≤r)=decide (0≤s)) : r=s := by
  have hiff : (0≤r)↔(0≤s) := decide_eq_decide.mp hsign
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · by_cases hr : 0≤r
    · have hs := hiff.mp hr
      linarith
    · have hs : ¬0≤s := mt hiff.mpr hr
      linarith

theorem ncard_j_G2Point_fiber_le (j : ℚ) :
    {P : G2Point ℚ | GoodCurve (F P.W) ∧ jValue (F P.W)=j}.ncard≤96 := by
  classical
  let S : Set (G2Point ℚ) := {P | GoodCurve (F P.W) ∧ jValue (F P.W)=j}
  let T : Set ℚ := {w | (jNumerator-C j*jDenominator).eval w=0}
  have : Finite T := (finite_j_parameter_roots j).to_subtype
  let f : S → T × (Bool × Bool × Bool) := fun P =>
    (⟨P.val.W,j_parameter_root_of_fiber j P.val P.property⟩,
      decide (0≤P.val.s1),decide (0≤P.val.s2),decide (0≤P.val.s3))
  have hf : Function.Injective f := by
    intro P Q he
    have hw : P.val.W=Q.val.W := congrArg (fun z : T × (Bool × Bool × Bool) => z.1.val) he
    have h1 := congrArg (fun z : T × (Bool × Bool × Bool) => z.2.1) he
    have h2 := congrArg (fun z : T × (Bool × Bool × Bool) => z.2.2.1) he
    have h3 := congrArg (fun z : T × (Bool × Bool × Bool) => z.2.2.2) he
    apply Subtype.ext
    apply G2Point.ext hw
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h1
      rw [P.val.s1_sq,Q.val.s1_sq,hw]
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h2
      rw [P.val.s2_sq,Q.val.s2_sq,hw]
    · apply rational_eq_of_sq_eq_and_sign _ _ _ h3
      rw [P.val.s3_sq,Q.val.s3_sq,hw]
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool=2 := by simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
  simp only [Nat.card_prod,hb] at hc
  have ht : T.ncard≤12 := ncard_j_parameter_roots_le j
  change Nat.card S≤96
  change Nat.card T≤12 at ht
  omega

theorem isCoprime_u_v_polynomial : IsCoprime uPolynomial vPolynomial := by
  refine ⟨C (-1406408618241/1095999610000:ℚ)*Polynomial.X+C (780479514441/547999805000:ℚ),
    C (-1406408618241/547999805000:ℚ)*Polynomial.X-C (1712919388059/273999902500:ℚ),?_⟩
  apply Polynomial.funext
  intro x
  norm_num [uPolynomial,vPolynomial,lambda]
  ring

private theorem coprime_invariant_parts {R : Type*} [CommRing R] (u v : R)
    (h : IsCoprime u v) : IsCoprime (u^2-3*v^2) (v^4*(u^2-4*v^2)) := by
  have hNv : IsCoprime (u^2-3*v^2) v := by
    convert (h.pow_left (m:=2)).add_mul_right_left (-3*v) using 1; ring
  have hND : IsCoprime (u^2-3*v^2) (u^2-4*v^2) := by
    convert ((hNv.pow_right (n:=2)).add_mul_right_right (-1)).neg_right using 1; ring
  exact hNv.pow_right.mul_right hND

theorem isCoprime_jNumerator_jDenominator : IsCoprime jNumerator jDenominator := by
  have h256 : IsUnit (256:ℚ[X]) := Polynomial.isUnit_C.mpr (by norm_num)
  unfold jNumerator jDenominator
  apply (isCoprime_mul_unit_left_left h256 _ _).2
  exact (coprime_invariant_parts _ _ isCoprime_u_v_polynomial).pow_left

def jRationalFunction : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) jNumerator/algebraMap ℚ[X] (RatFunc ℚ) jDenominator

private theorem denominator_poly_ne_zero : jDenominator≠0 := by
  intro h
  have hd := jDenominator_natDegree
  simp only [h,Polynomial.natDegree_zero] at hd
  contradiction

section Reduced
local instance secondJClassicalDecidableEq : DecidableEq ℚ := Classical.decEq ℚ

private theorem j_parts_gcd_one : gcd jNumerator jDenominator=1 := by
  have hu := isCoprime_jNumerator_jDenominator.isUnit_of_dvd' (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  have hn := normalize_eq_one.mpr hu
  rwa [normalize_gcd] at hn

theorem jRationalFunction_num_natDegree : jRationalFunction.num.natDegree=12 := by
  classical
  unfold jRationalFunction
  rw [RatFunc.num_div,j_parts_gcd_one,EuclideanDomain.div_one,EuclideanDomain.div_one,
    Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr denominator_poly_ne_zero))]
  exact jNumerator_natDegree

theorem jRationalFunction_denom_natDegree : jRationalFunction.denom.natDegree=11 := by
  classical
  unfold jRationalFunction
  rw [RatFunc.denom_div _ denominator_poly_ne_zero,j_parts_gcd_one,EuclideanDomain.div_one,
    Polynomial.natDegree_C_mul (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr denominator_poly_ne_zero))]
  exact jDenominator_natDegree

theorem jRationalFunction_map_degree :
    max jRationalFunction.num.natDegree jRationalFunction.denom.natDegree=12 := by
  rw [jRationalFunction_num_natDegree,jRationalFunction_denom_natDegree]
  decide

end Reduced
end
end Z2Z4Rank6.SecondFamily
