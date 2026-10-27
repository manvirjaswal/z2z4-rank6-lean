module

public import Z2Z4Rank6.TwistSelmerDataBitsQ2
public import Z2Z4Rank6.TwistSelmerDataConstraints

@[expose] public section

/-! Semantic local/support rows and exact closed support facts.
For Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
open scoped BigOperators

def q2PrimeConstraints : Fin 51 → PrimeConstraint 18 :=
  ![.zero 0 0,
    .zero 0 1,
    .zero 0 12,
    .zero 0 13,
    .zero 0 14,
    .zero 0 16,
    .zero 1 3,
    .zero 1 4,
    .zero 1 5,
    .zero 1 6,
    .zero 1 7,
    .zero 1 10,
    .zero 2 8,
    .zero 2 9,
    .zero 2 11,
    .zero 2 15,
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
    .character 2 8 ![0,0,0],
    .character 2 9 ![0,0,0],
    .zero 0 11,
    .character 2 15 ![0,0,0],
    .character 1 3 ![0,0,0],
    .character 1 4 ![0,0,0],
    .character 1 5 ![0,0,0],
    .zero 0 6,
    .character 1 7 ![0,0,0],
    .character 1 10 ![0,0,0],
    .character 0 17 ![0,0,0],
    .character 1 17 ![1,1,0],
    .character 0 1 ![0,1,0],
    .character 0 12 ![0,0,0],
    .character 0 13 ![0,1,0],
    .character 0 14 ![0,1,0],
    .character 0 16 ![0,0,0]]

theorem q2Primes_injective : Function.Injective q2Primes := by decide +kernel

theorem q2Primes_prime (j : Fin 18) : (q2Primes j).Prime := by
  fin_cases j <;> norm_num [q2Primes]

theorem q2SupportPower (c : Fin 3) :
    ![r2 1*r3 1,r2 1*(r2 1-r3 1),r3 1*(r2 1-r3 1)] c ∣
      ((∏ i, q2Primes i : ℕ) : ℤ)^8 := by
  fin_cases c <;> norm_num [r2,r3,D,A,B,q2Primes,Fin.prod_univ_succ]

end Z2Z4Rank6.TwistSelmer
