module

public import Z2Z4Rank6.ECProjectiveSchemeInfinity
public import Z2Z4Rank6.PlaneHypersurfaceSmooth

@[expose] public section

/-! Smoothness of the Y-chart of the printed projective cubic.
Euler's identity puts z in the derivative ideal; the cubic then puts x³ in
it, while the z derivative puts 1−x² in it. These imply 1 is in that ideal.
Source: Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
-/
namespace Z2Z4Rank6.ECProjectiveSchemeInfinity
noncomputable section
open scoped Classical
open AlgebraicGeometry

abbrev partialDerivative (i:Fin 2) : CoordinateRing := PlaneHypersurfaceSmooth.derivative (relation 0) i

private theorem relation_C : relation 0=
    MvPolynomial.X 1-MvPolynomial.X 0^3-MvPolynomial.X 0^2*MvPolynomial.X 1+
      MvPolynomial.C (137620:ℚ)*MvPolynomial.X 0*MvPolynomial.X 1^2+
      MvPolynomial.C (10504000:ℚ)*MvPolynomial.X 1^3 := by
  simp only [relation,map_ofNat]

theorem partial_zero : partialDerivative 0= -3*x^2-2*x*z+137620*z^2 := by
  change Ideal.Quotient.mk definingIdeal (MvPolynomial.pderiv _ (relation 0))=_
  rw [relation_C]
  simp only [map_sub,map_add,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X]
  norm_num [x,z,map_ofNat]
  ring

theorem partial_one : partialDerivative 1=1-x^2+275240*x*z+31512000*z^2 := by
  change Ideal.Quotient.mk definingIdeal (MvPolynomial.pderiv _ (relation 0))=_
  rw [relation_C]
  simp only [map_sub,map_add,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X]
  norm_num [x,z,map_ofNat]
  ring

private theorem mem_of_unit_mul_mem {R:Type*} [CommRing R] (I:Ideal R)
    (a b:R) (ha:IsUnit a) (h:a*b∈I) : b∈I := by
  obtain ⟨a,rfl⟩ := ha
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using I.mul_mem_left (↑a⁻¹) h

/-- The derivative ideal is the unit ideal, including the infinity point. -/
theorem partials_span_top : Ideal.span (Set.range partialDerivative)=⊤ := by
  let J : Ideal CoordinateRing := Ideal.span (Set.range partialDerivative)
  have h0 : partialDerivative 0∈J := Ideal.subset_span ⟨0,rfl⟩
  have h1 : partialDerivative 1∈J := Ideal.subset_span ⟨1,rfl⟩
  have hz : z∈J := by
    apply mem_of_unit_mul_mem J (algebraMap ℚ CoordinateRing 2) z
      ((isUnit_iff_ne_zero.mpr (by norm_num: (2:ℚ)≠0)).map (algebraMap ℚ CoordinateRing))
    have he : -(x*partialDerivative 0+z*partialDerivative 1)=2*z := by
      rw [partial_zero,partial_one]
      linear_combination -3*equation
    simpa only [map_ofNat,←he] using J.neg_mem
      (J.add_mem (J.mul_mem_left x h0) (J.mul_mem_left z h1))
  have hb : 1-x^2∈J := by
    have he : 1-x^2=partialDerivative 1-(275240*x+31512000*z)*z := by rw [partial_one];ring
    rw [he]
    exact J.sub_mem h1 (J.mul_mem_left _ hz)
  have hx3 : x^3∈J := by
    have he : x^3=(1-x^2+137620*x*z+10504000*z^2)*z := by
      linear_combination -equation
    rw [he]
    exact J.mul_mem_left _ hz
  apply (Ideal.eq_top_iff_one _).mpr
  change (1:CoordinateRing)∈J
  have he : (1:CoordinateRing)=(1+x^2)*(1-x^2)+x*x^3 := by ring
  rw [he]
  exact J.add_mem (J.mul_mem_left _ hb) (J.mul_mem_left x hx3)

instance structureMap_smooth : SmoothOfRelativeDimension 1 structureMap := by
  exact PlaneHypersurfaceSmooth.structureMap_smooth (relation 0) partials_span_top

end
end Z2Z4Rank6.ECProjectiveSchemeInfinity
