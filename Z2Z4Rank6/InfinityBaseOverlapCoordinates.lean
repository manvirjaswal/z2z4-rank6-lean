import Z2Z4Rank6.InfinityBaseOverlapMap
import Z2Z4Rank6.LaurentCechQuotient

/-! Infinity restriction coordinates in the Laurent overlap.
Each polynomial in Z becomes a polynomial in M⁻¹; the basis entries have
weights 0,1,1,2, giving the precise four negative exponent bounds. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section
open scoped BigOperators

abbrev infinityBasis := InfinityBaseNormalForm.coordinateBasis

def reversePolynomial : Poly→+*Laurent :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

@[simp] theorem reversePolynomial_X : reversePolynomial Polynomial.X=LaurentPolynomial.T (-1) :=
  Polynomial.eval₂_X _ _

theorem reversePolynomial_eq_invert (p : Poly) :
    reversePolynomial p=LaurentPolynomial.invert (Polynomial.toLaurent p) := by
  have hh : reversePolynomial=LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp [reversePolynomial_X]
  exact RingHom.congr_fun hh p

theorem reversePolynomial_injective : Function.Injective reversePolynomial := by
  intro p q h
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  simpa only [←reversePolynomial_eq_invert] using h

theorem infinityRestriction_polynomial (p : Poly) :
    infinityRestriction (InfinityBaseNormalForm.polynomialToCoordinate p)=
      algebraMap Laurent OverlapRing (reversePolynomial p) := by
  have hh : infinityRestriction.toRingHom.comp InfinityBaseNormalForm.polynomialToCoordinate=
      (algebraMap Laurent OverlapRing).comp reversePolynomial := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change infinityRestriction (InfinityBaseNormalForm.polynomialToCoordinate Polynomial.X)=
        algebraMap Laurent OverlapRing (reversePolynomial Polynomial.X)
      rw [InfinityBaseNormalForm.polynomialToCoordinate_X,infinityRestriction_z,reversePolynomial_X,
        scalarLaurent_T_neg_one]
  exact RingHom.congr_fun hh p

theorem scalarLaurent_T_neg_two : algebraMap Laurent OverlapRing (LaurentPolynomial.T (-2))=inverseM^2 := by
  have ht : (LaurentPolynomial.T (-2):Laurent)=(LaurentPolynomial.T (-1))^2 := by
    rw [LaurentPolynomial.T_pow]
    norm_num
  rw [ht,map_pow,scalarLaurent_T_neg_one]

theorem infinityRestriction_basis (i : Fin 4) :
    infinityRestriction (infinityBasis i)=
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (-LaurentCechQuotient.weights i))*overlapBasis i := by
  unfold infinityBasis
  fin_cases i
  · change infinityRestriction (InfinityBaseNormalForm.coordinateBasis (0:Fin 4))=
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (0:ℤ))*overlapBasis 0
    rw [InfinityBaseNormalForm.coordinateBasis_zero,map_one,overlapBasis_zero]
    simp only [LaurentPolynomial.T_zero,map_one,mul_one]
  · change infinityRestriction (InfinityBaseNormalForm.coordinateBasis (1:Fin 4))=
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (-1:ℤ))*overlapBasis 1
    rw [InfinityBaseNormalForm.coordinateBasis_one,infinityRestriction_u,overlapBasis_one]
    rw [scalarLaurent_T_neg_one]
    exact mul_comm (algebraMap CoordinateRing OverlapRing AffineBaseScheme.u) inverseM
  · change infinityRestriction (InfinityBaseNormalForm.coordinateBasis (2:Fin 4))=
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (-1:ℤ))*overlapBasis 2
    rw [InfinityBaseNormalForm.coordinateBasis_two,infinityRestriction_v,overlapBasis_two]
    rw [scalarLaurent_T_neg_one]
    exact mul_comm (algebraMap CoordinateRing OverlapRing AffineBaseScheme.v) inverseM
  · change infinityRestriction (InfinityBaseNormalForm.coordinateBasis (3:Fin 4))=
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (-2:ℤ))*overlapBasis 3
    rw [InfinityBaseNormalForm.coordinateBasis_three,map_mul,infinityRestriction_u,infinityRestriction_v,
      overlapBasis_three,map_mul]
    rw [scalarLaurent_T_neg_two]
    ring

theorem infinityRestriction_expansion (c : ProjectiveBaseSchemeCharts.InfinityCoordinateRing) :
    infinityRestriction c=∑i:Fin 4,
      (reversePolynomial (infinityBasis.repr c i)*LaurentPolynomial.T (-LaurentCechQuotient.weights i)) • overlapBasis i := by
  nth_rw 1 [←infinityBasis.sum_repr c]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul]
  change infinityRestriction (InfinityBaseNormalForm.polynomialToCoordinate (infinityBasis.repr c i))*
      infinityRestriction (infinityBasis i)=_
  rw [infinityRestriction_polynomial,infinityRestriction_basis]
  simp only [Algebra.smul_def,map_mul,mul_assoc]

theorem overlapCoordinates_infinityRestriction
    (c : ProjectiveBaseSchemeCharts.InfinityCoordinateRing) (i : Fin 4) :
    overlapCoordinates (infinityRestriction c) i=
      reversePolynomial (infinityBasis.repr c i)*LaurentPolynomial.T (-LaurentCechQuotient.weights i) := by
  change overlapBasis.repr (infinityRestriction c) i=_
  rw [infinityRestriction_expansion]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  simp [Finsupp.single_apply]
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
