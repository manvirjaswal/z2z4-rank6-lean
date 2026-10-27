import Z2Z4Rank6.GTwistSelmerBitsH
import Z2Z4Rank6.GTwistSelmerLocal
import Z2Z4Rank6.TwistSelmerDataNecessary
import Z2Z4Rank6.SplitRealConditions

/-! Semantic support/local row labels for the extra h-twist covering.
Source: Jaswal Proposition 7.2(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTwistSelmer

open scoped BigOperators
open TwistSelmer
noncomputable section

def hPrimeConstraints : Fin 50 → PrimeConstraint 18 :=
  ![.zero 0 0,
    .zero 0 2,
    .zero 0 3,
    .zero 0 13,
    .zero 0 14,
    .zero 0 16,
    .zero 1 7,
    .zero 1 8,
    .zero 1 10,
    .zero 1 11,
    .zero 2 4,
    .zero 2 5,
    .zero 2 6,
    .zero 2 9,
    .zero 2 12,
    .product 0,
    .product 1,
    .product 2,
    .product 3,
    .product 4,
    .product 5,
    .product 6,
    .product 7,
    .product 8,
    .product 9,
    .product 10,
    .product 11,
    .product 12,
    .product 13,
    .product 14,
    .product 15,
    .product 16,
    .product 17,
    .character 2 4 ![0,0,0],
    .character 2 5 ![0,0,0],
    .character 2 6 ![0,0,0],
    .character 2 9 ![0,0,0],
    .character 2 12 ![0,0,0],
    .character 1 7 ![0,0,0],
    .character 1 8 ![0,0,0],
    .character 1 10 ![0,0,0],
    .character 1 11 ![0,0,0],
    .character 0 15 ![0,0,0],
    .character 1 15 ![1,1,0],
    .character 0 17 ![1,0,0],
    .character 1 17 ![0,0,0],
    .character 0 3 ![0,1,0],
    .character 0 13 ![0,0,0],
    .character 0 14 ![0,1,0],
    .character 0 16 ![0,0,0]]

theorem hPrimes_injective : Function.Injective hPrimes := by decide +kernel

theorem hPrimes_prime (j : Fin 18) : (hPrimes j).Prime := by
  fin_cases j <;> norm_num [hPrimes]

theorem hSupportPower (c : Fin 3) :
    rootProduct r2 r3 c∣((∏ i, hPrimes i : ℕ) : ℤ)^8 := by
  fin_cases c <;> norm_num [rootProduct,r2,r3,D,A,B,hPrimes,Fin.prod_univ_succ]

theorem hCoefficient_squarefree (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (c : Fin 3) : Squarefree (coefficient d c) :=
  coefficient_squarefree_of_mem d r2 r3 hd c

theorem hCoefficient_support (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (c : Fin 3) : (coefficient d c).natAbs∣(∏ i, hPrimes i)^8 :=
  coefficient_support_bound hPrimes d r2 r3 8 hSupportPower hd c

theorem hSecond_positive (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    0<d.2.1 :=
  splitCover_second_pos_of_ordered_differences d r2 r3 roots_ordered.1 roots_ordered.2
    hd.1.ne_zero hd.2.1.ne_zero hd.2.2.1.ne_zero hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2

/-- The canonical integer covering is exactly recovered from its
sign/divisibility bits in the finite prime pool. -/
theorem hCandidate_reconstruct (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    candidate hPrimes (bitVector hPrimes d)=d :=
  candidate_bitVector hPrimes hPrimes_injective hPrimes_prime d 8
    (hCoefficient_squarefree d hd) (hCoefficient_support d hd) (hSecond_positive d hd)
    hd.2.2.2.2.2.2.1

/-- Every semantic row evaluates on the bit vector to its
support/product/local character value. -/
theorem hConstraint_source (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (i : Fin 50) :
    constraintRow hPrimes (hPrimeConstraints i) ⬝ᵥ bitVector hPrimes d=
      constraintValue hPrimes d (hPrimeConstraints i) :=
  constraintRow_source hPrimes hPrimes_injective hPrimes_prime d 8
    (hCoefficient_squarefree d hd) (hCoefficient_support d hd) (hSecond_positive d hd)
    hd.2.2.2.2.2.2.1 (hPrimeConstraints i)

end
end Z2Z4Rank6.GTwistSelmer
