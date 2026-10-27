module

public import Z2Z4Rank6.SecondTorsionCoverInfinityRestriction
public import Z2Z4Rank6.InfinityBaseOverlapCoordinates

@[expose] public section

/-! Exact weighted coordinates of the signed-cover infinity
restriction. The basis entries acquire weights 0,1,1,2,2,3,3,4;
polynomials in the infinity parameter become reversed Laurent
polynomials.
Source: Jaswal, Section 8, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondTorsionCoverOverlap
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

private def naturalWeights : Fin 8 → ℕ := ![0,1,1,2,2,3,3,4]

private theorem weights_eq_natural (i : Fin 8) :
    SecondTorsionCoverLaurent.weights i = (naturalWeights i : ℤ) := by
  fin_cases i <;> rfl

theorem infinityRestriction_basis (ε : Bool) (i : Fin 8) :
    infinityRestriction ε (infinityBasis ε i) =
      algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-SecondTorsionCoverLaurent.weights i)) *
        overlapBasis ε i := by
  rw [weights_eq_natural,scalarLaurent_T_neg_nat,overlapBasis_apply]
  simp only [infinityBasis,affineBasis,SecondTorsionCoverInfinity.basis,SecondTorsionCoverAffine.basis]
  fin_cases i <;> simp [naturalWeights] <;> ring

theorem infinityRestriction_expansion (ε : Bool) (c : InfinityRing ε) :
    infinityRestriction ε c = ∑ i : Fin 8,
      (AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis ε).repr c i) *
        LaurentPolynomial.T (-SecondTorsionCoverLaurent.weights i)) • overlapBasis ε i := by
  nth_rw 1 [←(infinityBasis ε).sum_repr c]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul]
  change infinityRestriction ε
      (TripleSquareCover.polynomialToCoordinate (SecondTorsionCoverInfinity.radicand ε)
        ((infinityBasis ε).repr c i)) *
      infinityRestriction ε (infinityBasis ε i) = _
  rw [infinityRestriction_polynomial,infinityRestriction_basis]
  simp only [Algebra.smul_def,map_mul,mul_assoc]
  rfl

theorem overlapCoordinates_infinityRestriction (ε : Bool) (c : InfinityRing ε) (i : Fin 8) :
    overlapCoordinates ε (infinityRestriction ε c) i =
      AffineBaseFunctionFieldIso.reversePolynomial ((infinityBasis ε).repr c i) *
        LaurentPolynomial.T (-SecondTorsionCoverLaurent.weights i) := by
  change (overlapBasis ε).repr (infinityRestriction ε c) i = _
  rw [infinityRestriction_expansion]
  simp only [map_sum,map_smul,Module.Basis.repr_self]
  simp [Finsupp.single_apply]

end
end Z2Z4Rank6.SecondTorsionCoverOverlap
