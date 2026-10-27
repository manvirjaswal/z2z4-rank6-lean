import Z2Z4Rank6.TwistSelmerDataBitsQ1
import Z2Z4Rank6.TwistSelmerDataConstraints

/-! Semantic local/support rows and exact closed support facts.
For Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
open scoped BigOperators

def q1PrimeConstraints : Fin 42 → PrimeConstraint 16 :=
  ![.zero 0 3,
    .zero 0 10,
    .zero 0 11,
    .zero 0 15,
    .zero 1 4,
    .zero 1 5,
    .zero 1 9,
    .zero 1 13,
    .zero 2 6,
    .zero 2 7,
    .zero 2 8,
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
    .character 2 6 ![0,0,0],
    .character 2 7 ![0,0,0],
    .zero 0 8,
    .character 2 12 ![0,0,0],
    .character 1 4 ![0,0,0],
    .zero 0 5,
    .character 1 9 ![0,0,0],
    .character 1 13 ![0,0,0],
    .character 0 14 ![0,0,0],
    .character 1 14 ![1,0,0],
    .character 0 3 ![0,0,0],
    .character 0 10 ![0,1,0],
    .character 0 11 ![0,1,0],
    .character 0 15 ![0,1,0]]

theorem q1Primes_injective : Function.Injective q1Primes := by decide +kernel

theorem q1Primes_prime (j : Fin 16) : (q1Primes j).Prime := by
  fin_cases j <;> norm_num [q1Primes]

theorem q1SupportPower (c : Fin 3) :
    ![r2 0*r3 0,r2 0*(r2 0-r3 0),r3 0*(r2 0-r3 0)] c ∣
      ((∏ i, q1Primes i : ℕ) : ℤ)^8 := by
  fin_cases c <;> norm_num [r2,r3,D,A,B,q1Primes,Fin.prod_univ_succ]

end Z2Z4Rank6.TwistSelmer
