import Z2Z4Rank6.ECProjectiveSchemeAffine
import Z2Z4Rank6.PlaneHypersurfaceSmooth
import Z2Z4Rank6.ECFunctionField
import Mathlib.FieldTheory.Separable

/-! Smoothness of the printed affine EC quotient. Distinct roots
404,−325,−80 give f/f' Bezout; the two partials generate the unit ideal.
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
-/
namespace Z2Z4Rank6.ECProjectiveSchemeAffine
noncomputable section
open scoped Classical BigOperators
open AlgebraicGeometry Polynomial

abbrev partialDerivative (i:Fin 2) : CoordinateRing := PlaneHypersurfaceSmooth.derivative (relation 0) i

private theorem relation_C : relation 0=
    MvPolynomial.X 1^2-MvPolynomial.X 0^3-MvPolynomial.X 0^2+
      MvPolynomial.C (137620:ℚ)*MvPolynomial.X 0+MvPolynomial.C (10504000:ℚ) := by
  simp only [relation,map_ofNat]

theorem partial_zero : partialDerivative 0= -3*x^2-2*x+137620 := by
  change Ideal.Quotient.mk definingIdeal (MvPolynomial.pderiv _ (relation 0))=_
  rw [relation_C]
  simp only [map_sub,map_add,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X]
  norm_num [x,map_ofNat]
  ring

theorem partial_one : partialDerivative 1=2*y := by
  change Ideal.Quotient.mk definingIdeal (MvPolynomial.pderiv _ (relation 0))=_
  rw [relation_C]
  simp only [map_sub,map_add,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X]
  norm_num [y,map_ofNat]

private theorem cubic_separable : ECFunctionField.cubicPolynomial.Separable := by
  have hf : ECFunctionField.cubicPolynomial=
      ∏i:Fin 3,(Polynomial.X-C ((![404,-325,-80]:Fin 3→ℚ) i)) := by
    simp [ECFunctionField.cubicPolynomial,Fin.prod_univ_succ]
    norm_num only [map_ofNat]
    ring
  rw [hf]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr (by decide +kernel)

private theorem eval_cubic : (Polynomial.aeval x) ECFunctionField.cubicPolynomial=y^2 := by
  simp only [ECFunctionField.cubicPolynomial,map_add,map_sub,map_mul,map_pow,map_ofNat,
    aeval_X]
  exact equation.symm

private theorem eval_cubic_derivative :
    (Polynomial.aeval x) ECFunctionField.cubicPolynomial.derivative= -partialDerivative 0 := by
  rw [partial_zero]
  norm_num [ECFunctionField.cubicPolynomial,derivative_add,derivative_sub,derivative_pow]
  norm_num only [map_ofNat]
  ring

private theorem mem_of_unit_mul_mem {R:Type*} [CommRing R] (I:Ideal R)
    (a b:R) (ha:IsUnit a) (h:a*b∈I) : b∈I := by
  obtain ⟨a,rfl⟩ := ha
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using I.mul_mem_left (↑a⁻¹) h

/-- The two partialDerivative derivatives generate the whole coordinate ring. -/
theorem partials_span_top : Ideal.span (Set.range partialDerivative)=⊤ := by
  let J : Ideal CoordinateRing := Ideal.span (Set.range partialDerivative)
  have h0 : partialDerivative 0∈J := Ideal.subset_span ⟨0,rfl⟩
  have h1 : partialDerivative 1∈J := Ideal.subset_span ⟨1,rfl⟩
  have hy : y∈J := by
    apply mem_of_unit_mul_mem J (algebraMap ℚ CoordinateRing 2) y
      ((isUnit_iff_ne_zero.mpr (by norm_num: (2:ℚ)≠0)).map (algebraMap ℚ CoordinateRing))
    simpa only [map_ofNat,partial_one] using h1
  obtain ⟨A,B,hAB⟩ := cubic_separable
  have he := congrArg (Polynomial.aeval x) hAB
  simp only [map_add,map_mul,map_one,eval_cubic,eval_cubic_derivative] at he
  apply (Ideal.eq_top_iff_one _).mpr
  change (1:CoordinateRing)∈J
  rw [←he]
  exact J.add_mem (J.mul_mem_left _ (by simpa only [sq] using J.mul_mem_left y hy))
    (J.mul_mem_left _ (J.neg_mem h0))

/-- Mathlib relative-dimension-one smoothness of the affine chart. -/
instance structureMap_smooth : SmoothOfRelativeDimension 1 structureMap := by
  exact PlaneHypersurfaceSmooth.structureMap_smooth (relation 0) partials_span_top

end
end Z2Z4Rank6.ECProjectiveSchemeAffine
