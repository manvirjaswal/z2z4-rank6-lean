module

public import Z2Z4Rank6.SecondFamily
public import Z2Z4Rank6.JInvariant

@[expose] public section

/-!
# Finite fibers of the second family's j-invariant

The final j-invariant argument in Theorem 8.1(c) of Jaswal,
DOI 10.5281/zenodo.23437117. The curves and the G₂ points are objects;
nonconstant j and finite fibers are proved by polynomial root bounds.
-/

namespace Z2Z4Rank6.SecondFamily
open Polynomial Set
noncomputable section

def uPolynomial : ℚ[X] := 2*(1+C (lambda:ℚ))^2*Polynomial.X+2*(Polynomial.X+C (lambda:ℚ))^2
def vPolynomial : ℚ[X] := -(Polynomial.X-1)*(Polynomial.X-C ((lambda:ℚ)^2))
def jNumerator : ℚ[X] := 256*(uPolynomial^2-3*vPolynomial^2)^3
def jDenominator : ℚ[X] := vPolynomial^4*(uPolynomial^2-4*vPolynomial^2)

@[simp] theorem uPolynomial_eval (w : ℚ) : uPolynomial.eval w=U w := by simp [uPolynomial,U]
@[simp] theorem vPolynomial_eval (w : ℚ) : vPolynomial.eval w=V w := by simp [vPolynomial,V]

theorem j_fiber_polynomial_ne_zero (j : ℚ) : jNumerator-C j*jDenominator≠0 := by
  intro h
  have he := congrArg (Polynomial.eval (1:ℚ)) h
  norm_num [jNumerator,jDenominator,uPolynomial,vPolynomial,lambda] at he

theorem finite_j_parameter_roots (j : ℚ) :
    {w : ℚ | (jNumerator-C j*jDenominator).eval w=0}.Finite :=
  Polynomial.finite_setOfPred_isRoot (j_fiber_polynomial_ne_zero j)

theorem finite_G2Point_W_fiber (w : ℚ) : {P : G2Point ℚ | P.W=w}.Finite := by
  have h1 := Z2Z4Rank6.finite_square_roots w
  have h2 := Z2Z4Rank6.finite_square_roots (qA w)
  have h3 := Z2Z4Rank6.finite_square_roots (qB w)
  let f : G2Point ℚ → ℚ × ℚ × ℚ := fun P => (P.s1,P.s2,P.s3)
  have hi : f '' {P : G2Point ℚ | P.W=w} ⊆
      {r : ℚ | r^2=w} ×ˢ ({r : ℚ | r^2=qA w} ×ˢ {r : ℚ | r^2=qB w}) := by
    rintro _ ⟨P,hP,rfl⟩
    change P.W=w at hP
    exact ⟨by simpa [f,hP] using P.s1_sq,
      by simpa [f,hP] using P.s2_sq,by simpa [f,hP] using P.s3_sq⟩
  exact ((h1.prod (h2.prod h3)).subset hi).of_finite_image (by
    intro P hP Q hQ he
    apply G2Point.ext (hP.trans hQ.symm)
    · exact congrArg Prod.fst he
    · exact congrArg (fun z : ℚ × ℚ × ℚ => z.2.1) he
    · exact congrArg (fun z : ℚ × ℚ × ℚ => z.2.2) he)

theorem jDenominator_ne_zero (w : ℚ) (h : GoodCurve (F w)) : jDenominator.eval w≠0 := by
  have hD : (F w).Δ=16*jDenominator.eval w := by
    rw [F_discriminant]
    simp [jDenominator,mul_assoc]
  intro hd
  have hz := h.isUnit.ne_zero
  rw [hD,hd,mul_zero] at hz
  exact hz rfl

theorem jValue_F_eq (w : ℚ) (_h : GoodCurve (F w)) :
    jValue (F w)=jNumerator.eval w/jDenominator.eval w := by
  have hD : (F w).Δ=16*jDenominator.eval w := by
    rw [F_discriminant]
    simp [jDenominator,mul_assoc]
  have hN : (F w).c₄^3=16*jNumerator.eval w := by
    simp only [jNumerator,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
      Polynomial.eval_sub,uPolynomial_eval,vPolynomial_eval,F,twistedF,
      WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
    ring
  unfold jValue
  rw [hD,hN]
  field_simp

theorem j_parameter_root_of_fiber (j : ℚ) (P : G2Point ℚ)
    (h : GoodCurve (F P.W) ∧ jValue (F P.W)=j) :
    (jNumerator-C j*jDenominator).eval P.W=0 := by
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  have he : jNumerator.eval P.W/jDenominator.eval P.W=j :=
    (jValue_F_eq P.W h.1).symm.trans h.2
  exact sub_eq_zero.mpr ((div_eq_iff (jDenominator_ne_zero P.W h.1)).mp he)

theorem finite_j_G2Point_fiber (j : ℚ) :
    {P : G2Point ℚ | GoodCurve (F P.W) ∧ jValue (F P.W)=j}.Finite := by
  have hf := (finite_j_parameter_roots j).preimage' (fun w _ => finite_G2Point_W_fiber w)
  exact hf.subset (fun P hP => j_parameter_root_of_fiber j P hP)

/-- Any infinite set of desired second-family fibers gives infinitely many
rational j-invariants and hence the printed main theorem. -/
theorem theorem11_of_infinite_desired_fibers (S : Set (G2Point ℚ)) (hS : S.Infinite)
    (hcurves : ∀ P∈S, DesiredCurve (F P.W)) : Theorem11 := by
  apply Z2Z4Rank6.theorem11_of_infinite_j
  have hi : ((fun P : G2Point ℚ => jValue (F P.W)) '' S).Infinite := by
    intro hfinite
    apply hS
    apply Set.Finite.of_finite_fibers (fun P : G2Point ℚ => jValue (F P.W)) hfinite
    intro j _
    exact (finite_j_G2Point_fiber j).subset (fun P hP => ⟨(hcurves P hP.1).1,hP.2⟩)
  apply hi.mono
  rintro j ⟨P,hP,rfl⟩
  exact ⟨F P.W,hcurves P hP,rfl⟩

end
end Z2Z4Rank6.SecondFamily
