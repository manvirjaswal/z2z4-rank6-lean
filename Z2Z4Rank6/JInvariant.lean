module

public import Z2Z4Rank6.Statements
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite fibers of the j-invariant

The nonconstant rational function in the proof of Theorem 1.1 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

open Polynomial Set

/-- The numerator of the printed j-invariant, as a polynomial in m. -/
noncomputable def jNumerator : ℚ[X] :=
  256 * ((a Polynomial.X)^4 - (a Polynomial.X)^2 * (b Polynomial.X)^2 +
    (b Polynomial.X)^4)^3

/-- The denominator of the printed j-invariant, as a polynomial in m. -/
noncomputable def jDenominator : ℚ[X] :=
  (a Polynomial.X)^4 * (b Polynomial.X)^4 *
    ((a Polynomial.X)^2 - (b Polynomial.X)^2)^2

@[simp] theorem eval_a_poly (m : ℚ) : (a (Polynomial.X : ℚ[X])).eval m = a m := by
  simp [a]

@[simp] theorem eval_b_poly (m : ℚ) : (b (Polynomial.X : ℚ[X])).eval m = b m := by
  simp [b]

theorem eval_jNumerator (m : ℚ) : jNumerator.eval m =
    256 * ((a m)^4 - (a m)^2*(b m)^2 + (b m)^4)^3 := by
  simp [jNumerator]

theorem eval_jDenominator (m : ℚ) : jDenominator.eval m =
    (a m)^4 * (b m)^4 * ((a m)^2-(b m)^2)^2 := by
  simp [jDenominator]

/-- No constant multiple of the denominator is the numerator. The pole at m=1
already proves this, without relying on a numerical degree computation. -/
theorem j_fiber_polynomial_ne_zero (j : ℚ) :
    jNumerator - Polynomial.C j * jDenominator ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (1 : ℚ)) h
  norm_num [jNumerator, jDenominator, a, b] at he

/-- A fixed rational j-value imposes a nonzero polynomial equation on m. -/
theorem finite_j_parameter_roots (j : ℚ) :
    {m : ℚ | (jNumerator - Polynomial.C j * jDenominator).eval m = 0}.Finite :=
  Polynomial.finite_setOfPred_isRoot (j_fiber_polynomial_ne_zero j)

theorem finite_square_roots (q : ℚ) : {r : ℚ | r^2 = q}.Finite := by
  have hn : (Polynomial.X^2 - Polynomial.C q : ℚ[X]) ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) h
    norm_num at he
  have hf := Polynomial.finite_setOfPred_isRoot hn
  convert hf using 1
  ext r
  simp [Polynomial.IsRoot, sub_eq_zero]

/-- There are finitely many rational points of C above any fixed m. -/
theorem finite_CPoint_m_fiber (m : ℚ) : {c : CPoint | c.m = m}.Finite := by
  have hu := finite_square_roots (5*(3*m^2+242))
  have hv := finite_square_roots (5*(2*m^2+243))
  let f : CPoint → ℚ × ℚ := fun c => (c.u,c.v)
  have hi : f '' {c : CPoint | c.m = m} ⊆
      {r : ℚ | r^2 = 5*(3*m^2+242)} ×ˢ {r : ℚ | r^2 = 5*(2*m^2+243)} := by
    rintro _ ⟨c,hc,rfl⟩
    change c.m = m at hc
    exact ⟨by simpa [f, hc] using c.u_sq, by simpa [f, hc] using c.v_sq⟩
  exact ((hu.prod hv).subset hi).of_finite_image (by
    intro c hc d hd he
    apply CPoint.ext
    · exact hc.trans hd.symm
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he)

/-- The displayed rational expression is the j-invariant on every smooth
fiber. -/
theorem jValue_X_eq (m : ℚ) (h : GoodCurve (X m)) :
    jValue (X m) = jNumerator.eval m / jDenominator.eval m := by
  have hD : (X m).Δ = 16 * jDenominator.eval m := by
    rw [eval_jDenominator]
    simp only [X, E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hN : (X m).c₄^3 = 16 * jNumerator.eval m := by
    rw [eval_jNumerator]
    simp only [X, E, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hden : jDenominator.eval m ≠ 0 := by
    intro hd
    have hz := h.isUnit.ne_zero
    rw [hD, hd, mul_zero] at hz
    exact hz rfl
  unfold jValue
  rw [hD, hN]
  field_simp

theorem jDenominator_ne_zero (m : ℚ) (h : GoodCurve (X m)) :
    jDenominator.eval m ≠ 0 := by
  have hD : (X m).Δ = 16 * jDenominator.eval m := by
    rw [eval_jDenominator]
    simp only [X, E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  intro hd
  have hz := h.isUnit.ne_zero
  rw [hD, hd, mul_zero] at hz
  exact hz rfl

/-- Every rational j-value is attained at only finitely many smooth rational
fibers over C. -/
theorem finite_j_CPoint_fiber (j : ℚ) :
    {c : CPoint | GoodCurve (X c.m) ∧ jValue (X c.m) = j}.Finite := by
  have hf := (finite_j_parameter_roots j).preimage'
    (fun m _ => finite_CPoint_m_fiber m)
  apply hf.subset
  intro c hc
  change (jNumerator - Polynomial.C j * jDenominator).eval c.m = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  have he : jNumerator.eval c.m / jDenominator.eval c.m = j :=
    (jValue_X_eq c.m hc.1).symm.trans hc.2
  exact sub_eq_zero.mpr ((div_eq_iff (jDenominator_ne_zero c.m hc.1)).mp he)

/-- The final step of the paper: an infinite set of desired fibers over C
produces infinitely many j-invariants and hence Theorem 1.1. -/
theorem theorem11_of_infinite_desired_fibers (S : Set CPoint) (hS : S.Infinite)
    (hcurves : ∀ c ∈ S, DesiredCurve (X c.m)) : Theorem11 := by
  apply theorem11_of_infinite_j
  have himage : ((fun c : CPoint => jValue (X c.m)) '' S).Infinite := by
    intro hfinite
    apply hS
    apply Set.Finite.of_finite_fibers (fun c : CPoint => jValue (X c.m)) hfinite
    intro j _
    exact (finite_j_CPoint_fiber j).subset (by
      intro c hc
      exact ⟨(hcurves c hc.1).1, hc.2⟩)
  apply himage.mono
  rintro j ⟨c,hc,rfl⟩
  exact ⟨X c.m,hcurves c hc,rfl⟩

end Z2Z4Rank6
