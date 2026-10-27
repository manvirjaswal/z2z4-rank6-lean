module

public import Z2Z4Rank6.ThirdTwistCoverInfinityRestriction
public import Z2Z4Rank6.InfinityBaseOverlapCoordinates

@[expose] public section

/-! Exact weighted coordinates of the third-twist base infinity
restriction. The basis entries acquire weights 0,1,1,2,1,2,2,3;
polynomials in the infinity parameter become reversed Laurent
polynomials.
Source: Jaswal, Section 7, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwistCoverOverlap
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local simp] TripleSquareCover.coordinateBasis_zero
  TripleSquareCover.coordinateBasis_one TripleSquareCover.coordinateBasis_two
  TripleSquareCover.coordinateBasis_three TripleSquareCover.coordinateBasis_four
  TripleSquareCover.coordinateBasis_five TripleSquareCover.coordinateBasis_six
  TripleSquareCover.coordinateBasis_seven
  infinityRestriction_u infinityRestriction_v infinityRestriction_r

private def naturalWeights : Fin 8 → ℕ := ![0,1,1,2,1,2,2,3]

private theorem weights_eq_natural (i : Fin 8) :
    ThirdTwistCoverLaurent.weights i = (naturalWeights i : ℤ) := by
  fin_cases i <;> rfl

theorem infinityRestriction_basis  (i : Fin 8) :
    infinityRestriction (infinityBasis i) =
      algebraMap Laurent (OverlapRing) (LaurentPolynomial.T (-ThirdTwistCoverLaurent.weights i)) *
        overlapBasis i := by
  rw [weights_eq_natural,scalarLaurent_T_neg_nat,overlapBasis_apply]
  simp only [infinityBasis,affineBasis,ThirdTwistCoverInfinity.basis,ThirdTwistCoverAffine.basis]
  fin_cases i <;> simp [naturalWeights] <;> ring

theorem infinityRestriction_expansion  (c : InfinityRing) :
    infinityRestriction c = ∑ i : Fin 8,
      (AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis).repr c i) *
        LaurentPolynomial.T (-ThirdTwistCoverLaurent.weights i)) • overlapBasis i := by
  nth_rw 1 [←(infinityBasis).sum_repr c]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul]
  change infinityRestriction
      (TripleSquareCover.polynomialToCoordinate (ThirdTwistCoverInfinity.radicand)
        ((infinityBasis).repr c i)) *
      infinityRestriction (infinityBasis i) = _
  rw [infinityRestriction_polynomial,infinityRestriction_basis]
  simp only [Algebra.smul_def,map_mul,mul_assoc]
  rfl

theorem overlapCoordinates_infinityRestriction  (c : InfinityRing) (i : Fin 8) :
    overlapCoordinates (infinityRestriction c) i =
      AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis).repr c i) *
        LaurentPolynomial.T (-ThirdTwistCoverLaurent.weights i) := by
  change (overlapBasis).repr (infinityRestriction c) i = _
  rw [infinityRestriction_expansion]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end
end Z2Z4Rank6.ThirdTwistCoverOverlap
