module

public import Z2Z4Rank6.TwistSelmerDataRowsQ2
public import Z2Z4Rank6.TwistSelmerDataNecessary

@[expose] public section

/-! Concrete applications of proved support and odd-prime conditions.
Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

theorem q2Constraints_satisfied (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 1) (r3 1)) (i : Fin 51) :
    constraintValue q2Primes d (q2PrimeConstraints i)=0 := by
  fin_cases i
  · change constraintValue q2Primes d (.zero 0 0)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 1)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 12)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 13)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 14)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 16)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 7)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 1 10)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 2 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 2 9)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 2 11)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 2 15)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.product 0)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 0
  · change constraintValue q2Primes d (.product 1)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 1
  · change constraintValue q2Primes d (.product 2)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 2
  · change constraintValue q2Primes d (.product 3)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 3
  · change constraintValue q2Primes d (.product 4)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 4
  · change constraintValue q2Primes d (.product 5)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 5
  · change constraintValue q2Primes d (.product 6)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 6
  · change constraintValue q2Primes d (.product 7)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 7
  · change constraintValue q2Primes d (.product 8)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 8
  · change constraintValue q2Primes d (.product 9)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 9
  · change constraintValue q2Primes d (.product 10)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 10
  · change constraintValue q2Primes d (.product 11)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 11
  · change constraintValue q2Primes d (.product 12)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 12
  · change constraintValue q2Primes d (.product 13)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 13
  · change constraintValue q2Primes d (.product 14)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 14
  · change constraintValue q2Primes d (.product 15)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 15
  · change constraintValue q2Primes d (.product 16)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 16
  · change constraintValue q2Primes d (.product 17)=0
    exact product_constraint_of_mem q2Primes q2Primes_prime d (r2 1) (r3 1) hd 17
  · change constraintValue q2Primes d (.character 2 8 ![0,0,0])=0
    let : Fact (q2Primes 8).Prime := ⟨q2Primes_prime 8⟩
    apply first_square_character q2Primes 8 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 8) (r3 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 2 9 ![0,0,0])=0
    let : Fact (q2Primes 9).Prime := ⟨q2Primes_prime 9⟩
    apply first_square_character q2Primes 9 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 9) (r3 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 11)=0
    let : Fact (q2Primes 11).Prime := ⟨q2Primes_prime 11⟩
    apply first_nonsquare_zero q2Primes 11 d (r2 1) (r3 1) 5056243570169815 hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · norm_num [r2,r3,D,A,B,q2Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q2Primes 11) (r3 1)).mpr hsq
      exact (by decide +kernel : modularParity (q2Primes 11) (r3 1)≠0) he
  · change constraintValue q2Primes d (.character 2 15 ![0,0,0])=0
    let : Fact (q2Primes 15).Prime := ⟨q2Primes_prime 15⟩
    apply first_square_character q2Primes 15 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 15) (r3 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 1 3 ![0,0,0])=0
    let : Fact (q2Primes 3).Prime := ⟨q2Primes_prime 3⟩
    apply third_square_character q2Primes 3 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 3) (r2 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 1 4 ![0,0,0])=0
    let : Fact (q2Primes 4).Prime := ⟨q2Primes_prime 4⟩
    apply third_square_character q2Primes 4 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 4) (r2 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 1 5 ![0,0,0])=0
    let : Fact (q2Primes 5).Prime := ⟨q2Primes_prime 5⟩
    apply third_square_character q2Primes 5 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 5) (r2 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.zero 0 6)=0
    let : Fact (q2Primes 6).Prime := ⟨q2Primes_prime 6⟩
    apply third_nonsquare_zero q2Primes 6 d (r2 1) (r3 1) 36512766956480815 hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · norm_num [r2,r3,D,A,B,q2Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q2Primes 6) (r2 1)).mpr hsq
      exact (by decide +kernel : modularParity (q2Primes 6) (r2 1)≠0) he
  · change constraintValue q2Primes d (.character 1 7 ![0,0,0])=0
    let : Fact (q2Primes 7).Prime := ⟨q2Primes_prime 7⟩
    apply third_square_character q2Primes 7 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 7) (r2 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 1 10 ![0,0,0])=0
    let : Fact (q2Primes 10).Prime := ⟨q2Primes_prime 10⟩
    apply third_square_character q2Primes 10 d (r2 1) (r3 1) hd
    · norm_num [r2,r3,D,A,B,q2Primes]
    · exact (modularParity_eq_zero_iff (q2Primes 10) (r2 1)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
  · change constraintValue q2Primes d (.character 0 17 ![0,0,0])=0
    let : Fact (q2Primes 17).Prime := ⟨q2Primes_prime 17⟩
    have hv := shared_prime_characters q2Primes 17 d (r2 1) (r3 1) 4846592730610805 1468232871910805 hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q2Primes 17) (4846592730610805*1468232871910805)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q2Primes 17) (![-(1468232871910805),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.1
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q2Primes d (.character 1 17 ![1,1,0])=0
    let : Fact (q2Primes 17).Prime := ⟨q2Primes_prime 17⟩
    have hv := shared_prime_characters q2Primes 17 d (r2 1) (r3 1) 4846592730610805 1468232871910805 hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q2Primes 17) (4846592730610805*1468232871910805)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q2Primes 17) (![4846592730610805*(4846592730610805-1468232871910805),4846592730610805,1] c))=![1,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.2
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q2Primes d (.character 0 1 ![0,1,0])=0
    let : Fact (q2Primes 1).Prime := ⟨q2Primes_prime 1⟩
    have hv := simple_difference_character q2Primes 1 d (r2 1) (r3 1) hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q2Primes 1) (![1,-r2 1,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q2Primes d (.character 0 12 ![0,0,0])=0
    let : Fact (q2Primes 12).Prime := ⟨q2Primes_prime 12⟩
    have hv := simple_difference_character q2Primes 12 d (r2 1) (r3 1) hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q2Primes 12) (![1,-r2 1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q2Primes d (.character 0 13 ![0,1,0])=0
    let : Fact (q2Primes 13).Prime := ⟨q2Primes_prime 13⟩
    have hv := simple_difference_character q2Primes 13 d (r2 1) (r3 1) hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q2Primes 13) (![1,-r2 1,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q2Primes d (.character 0 14 ![0,1,0])=0
    let : Fact (q2Primes 14).Prime := ⟨q2Primes_prime 14⟩
    have hv := simple_difference_character q2Primes 14 d (r2 1) (r3 1) hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q2Primes 14) (![1,-r2 1,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q2Primes d (.character 0 16 ![0,0,0])=0
    let : Fact (q2Primes 16).Prime := ⟨q2Primes_prime 16⟩
    have hv := simple_difference_character q2Primes 16 d (r2 1) (r3 1) hd
      (by norm_num [r2,r3,D,A,B,q2Primes]) (by norm_num [r2,r3,D,A,B,q2Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 1) (r3 1) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q2Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q2Primes 16) (![1,-r2 1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv

end Z2Z4Rank6.TwistSelmer
