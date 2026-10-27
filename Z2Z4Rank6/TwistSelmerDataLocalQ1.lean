module

public import Z2Z4Rank6.TwistSelmerDataRowsQ1
public import Z2Z4Rank6.TwistSelmerDataNecessary

@[expose] public section

/-! Concrete applications of proved support and odd-prime conditions.
Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

theorem q1Constraints_satisfied (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 0) (r3 0)) (i : Fin 42) :
    constraintValue q1Primes d (q1PrimeConstraints i)=0 := by
  fin_cases i
  · change constraintValue q1Primes d (.zero 0 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 0 10)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 0 11)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 0 15)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 1 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 1 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 1 9)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 1 13)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 2 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 2 7)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 2 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 2 12)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.product 0)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 0
  · change constraintValue q1Primes d (.product 1)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 1
  · change constraintValue q1Primes d (.product 2)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 2
  · change constraintValue q1Primes d (.product 3)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 3
  · change constraintValue q1Primes d (.product 4)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 4
  · change constraintValue q1Primes d (.product 5)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 5
  · change constraintValue q1Primes d (.product 6)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 6
  · change constraintValue q1Primes d (.product 7)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 7
  · change constraintValue q1Primes d (.product 8)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 8
  · change constraintValue q1Primes d (.product 9)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 9
  · change constraintValue q1Primes d (.product 10)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 10
  · change constraintValue q1Primes d (.product 11)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 11
  · change constraintValue q1Primes d (.product 12)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 12
  · change constraintValue q1Primes d (.product 13)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 13
  · change constraintValue q1Primes d (.product 14)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 14
  · change constraintValue q1Primes d (.product 15)=0
    exact product_constraint_of_mem q1Primes q1Primes_prime d (r2 0) (r3 0) hd 15
  · change constraintValue q1Primes d (.character 2 6 ![0,0,0])=0
    let : Fact (q1Primes 6).Prime := ⟨q1Primes_prime 6⟩
    apply first_square_character q1Primes 6 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 6) (r3 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.character 2 7 ![0,0,0])=0
    let : Fact (q1Primes 7).Prime := ⟨q1Primes_prime 7⟩
    apply first_square_character q1Primes 7 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 7) (r3 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 0 8)=0
    let : Fact (q1Primes 8).Prime := ⟨q1Primes_prime 8⟩
    apply first_nonsquare_zero q1Primes 8 d (r2 0) (r3 0) 115558021036230 hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · norm_num [r2,r3,D,A,B,q1Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q1Primes 8) (r3 0)).mpr hsq
      exact (by decide +kernel : modularParity (q1Primes 8) (r3 0)≠0) he
  · change constraintValue q1Primes d (.character 2 12 ![0,0,0])=0
    let : Fact (q1Primes 12).Prime := ⟨q1Primes_prime 12⟩
    apply first_square_character q1Primes 12 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 12) (r3 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.character 1 4 ![0,0,0])=0
    let : Fact (q1Primes 4).Prime := ⟨q1Primes_prime 4⟩
    apply third_square_character q1Primes 4 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 4) (r2 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.zero 0 5)=0
    let : Fact (q1Primes 5).Prime := ⟨q1Primes_prime 5⟩
    apply third_nonsquare_zero q1Primes 5 d (r2 0) (r3 0) 357539513073270 hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · norm_num [r2,r3,D,A,B,q1Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q1Primes 5) (r2 0)).mpr hsq
      exact (by decide +kernel : modularParity (q1Primes 5) (r2 0)≠0) he
  · change constraintValue q1Primes d (.character 1 9 ![0,0,0])=0
    let : Fact (q1Primes 9).Prime := ⟨q1Primes_prime 9⟩
    apply third_square_character q1Primes 9 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 9) (r2 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.character 1 13 ![0,0,0])=0
    let : Fact (q1Primes 13).Prime := ⟨q1Primes_prime 13⟩
    apply third_square_character q1Primes 13 d (r2 0) (r3 0) hd
    · norm_num [r2,r3,D,A,B,q1Primes]
    · exact (modularParity_eq_zero_iff (q1Primes 13) (r2 0)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
  · change constraintValue q1Primes d (.character 0 14 ![0,0,0])=0
    let : Fact (q1Primes 14).Prime := ⟨q1Primes_prime 14⟩
    have hv := shared_prime_characters q1Primes 14 d (r2 0) (r3 0) 421373174320830 131071969000830 hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q1Primes 14) (421373174320830*131071969000830)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q1Primes 14) (![-(131071969000830),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.1
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q1Primes d (.character 1 14 ![1,0,0])=0
    let : Fact (q1Primes 14).Prime := ⟨q1Primes_prime 14⟩
    have hv := shared_prime_characters q1Primes 14 d (r2 0) (r3 0) 421373174320830 131071969000830 hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q1Primes 14) (421373174320830*131071969000830)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q1Primes 14) (![421373174320830*(421373174320830-131071969000830),421373174320830,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.2
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q1Primes d (.character 0 3 ![0,0,0])=0
    let : Fact (q1Primes 3).Prime := ⟨q1Primes_prime 3⟩
    have hv := simple_difference_character q1Primes 3 d (r2 0) (r3 0) hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q1Primes 3) (![1,-r2 0,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q1Primes d (.character 0 10 ![0,1,0])=0
    let : Fact (q1Primes 10).Prime := ⟨q1Primes_prime 10⟩
    have hv := simple_difference_character q1Primes 10 d (r2 0) (r3 0) hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q1Primes 10) (![1,-r2 0,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q1Primes d (.character 0 11 ![0,1,0])=0
    let : Fact (q1Primes 11).Prime := ⟨q1Primes_prime 11⟩
    have hv := simple_difference_character q1Primes 11 d (r2 0) (r3 0) hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q1Primes 11) (![1,-r2 0,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q1Primes d (.character 0 15 ![0,1,0])=0
    let : Fact (q1Primes 15).Prime := ⟨q1Primes_prime 15⟩
    have hv := simple_difference_character q1Primes 15 d (r2 0) (r3 0) hd
      (by norm_num [r2,r3,D,A,B,q1Primes]) (by norm_num [r2,r3,D,A,B,q1Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 0) (r3 0) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q1Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q1Primes 15) (![1,-r2 0,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv

end Z2Z4Rank6.TwistSelmer
