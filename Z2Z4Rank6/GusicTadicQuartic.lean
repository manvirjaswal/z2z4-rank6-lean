module

public import Z2Z4Rank6.GusicTadicFactorization
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Polynomial.GaussLemma

@[expose] public section

/-!
# Irreducibility of the quartic factor

The factor `m⁴−2m²+9801` in Proposition 2.3 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. A root is `5√2+7i`; its first four
powers are rationally independent by the irrationality of √2. This checks
the irreducibility needed to describe the squarefree polynomial divisors.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
open scoped BigOperators

noncomputable section

def quarticQ : ℚ[X] := Polynomial.X^4-2*Polynomial.X^2+9801

def quarticRoot : ℂ := 5*(Real.sqrt 2 : ℂ)+7*Complex.I

private theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ)^2=(2 : ℂ) := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

theorem quarticRoot_sq : quarticRoot^2=1+70*(Real.sqrt 2 : ℂ)*Complex.I := by
  unfold quarticRoot
  ring_nf
  rw [sqrt_two_complex_sq, Complex.I_sq]
  ring

theorem quarticRoot_cube : quarticRoot^3= -485*(Real.sqrt 2 : ℂ)+707*Complex.I := by
  rw [pow_succ, quarticRoot_sq]
  unfold quarticRoot
  ring_nf
  rw [sqrt_two_complex_sq, Complex.I_sq]
  ring

theorem quarticRoot_aeval : aeval quarticRoot quarticQ=0 := by
  change Polynomial.eval₂ (algebraMap ℚ ℂ) quarticRoot quarticQ=0
  simp only [quarticQ, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_ofNat]
  rw [show quarticRoot^4=(quarticRoot^2)^2 by ring, quarticRoot_sq]
  ring_nf
  rw [sqrt_two_complex_sq, Complex.I_sq]
  ring

private theorem rational_sqrt_two_separation (a b : ℚ)
    (h : (a : ℝ)+(b : ℝ)*Real.sqrt 2=0) : a=0 ∧ b=0 := by
  have hb : b=0 := by
    by_contra hb
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply irrational_sqrt_two
    refine ⟨-(a/b), ?_⟩
    push_cast
    rw [← neg_div]
    apply (div_eq_iff hbR).2
    nlinarith [h]
  constructor
  · rw [hb] at h
    norm_num at h
    exact_mod_cast h
  · exact hb

private theorem rat_algebraMap_complex (q : ℚ) : algebraMap ℚ ℂ q=(q : ℂ) := by
  simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℂ) q

theorem quarticRoot_powers_independent :
    LinearIndependent ℚ (fun i : Fin 4 => quarticRoot^i.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  rw [Fin.sum_univ_four] at hc
  simp only [Algebra.smul_def, rat_algebraMap_complex] at hc
  norm_num only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one] at hc
  change (c 0 : ℂ)+(c 1 : ℂ)*quarticRoot+(c 2 : ℂ)*quarticRoot^2+
    (c 3 : ℂ)*quarticRoot^3=0 at hc
  rw [quarticRoot_sq, quarticRoot_cube] at hc
  unfold quarticRoot at hc
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  norm_num [Complex.mul_re, Complex.mul_im] at hre him
  have hr := rational_sqrt_two_separation (c 0+c 2) (5*c 1-485*c 3)
    (by push_cast; linear_combination hre)
  have hi := rational_sqrt_two_separation (7*c 1+707*c 3) (70*c 2)
    (by push_cast; linear_combination him)
  intro i
  fin_cases i
  · change c 0=0
    nlinarith [hr.1, hr.2, hi.1, hi.2]
  · change c 1=0
    nlinarith [hr.1, hr.2, hi.1, hi.2]
  · change c 2=0
    nlinarith [hr.1, hr.2, hi.1, hi.2]
  · change c 3=0
    nlinarith [hr.1, hr.2, hi.1, hi.2]

/-- The printed quartic is irreducible over ℚ. -/
theorem quarticQ_irreducible : Irreducible quarticQ := by
  have hm : quarticQ.Monic := by unfold quarticQ; monicity!
  have hd : quarticQ.degree=4 := by unfold quarticQ; compute_degree!
  have he := minpoly.eq_of_linearIndependent ℚ quarticRoot hm quarticRoot_aeval 4 hd quarticRoot_powers_independent
  rw [← he]
  exact minpoly.irreducible ⟨quarticQ, hm, quarticRoot_aeval⟩

/-- The primitive integer quartic used in the divisor list is irreducible over ℤ. -/
theorem quarticFactor_irreducible : Irreducible quarticFactor := by
  have hm : quarticFactor.Monic := by unfold quarticFactor; monicity!
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm.isPrimitive).2
  have he : quarticFactor.map (Int.castRingHom ℚ)=quarticQ := by
    simp [quarticFactor, quarticQ]
  rw [he]
  exact quarticQ_irreducible

end

end Z2Z4Rank6.GusicTadic
