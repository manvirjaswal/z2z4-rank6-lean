module

public import Z2Z4Rank6.TwistSelmerDataRowsQ12
public import Z2Z4Rank6.TwistSelmerDataNecessary

@[expose] public section

/-! Concrete applications of proved support and odd-prime conditions.
Jaswal Proposition 5.2,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.TwistSelmer
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

theorem q12Constraints_satisfied (d : ECFullTriple)
    (hd : d∈fullTwoSelmerTriples (r2 2) (r3 2)) (i : Fin 52) :
    constraintValue q12Primes d (q12PrimeConstraints i)=0 := by
  fin_cases i
  · change constraintValue q12Primes d (.zero 0 2)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 12)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 13)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 14)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 16)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 7)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 1 10)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 2 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 2 9)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 2 11)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 2 15)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
    norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.product 0)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 0
  · change constraintValue q12Primes d (.product 1)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 1
  · change constraintValue q12Primes d (.product 2)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 2
  · change constraintValue q12Primes d (.product 3)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 3
  · change constraintValue q12Primes d (.product 4)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 4
  · change constraintValue q12Primes d (.product 5)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 5
  · change constraintValue q12Primes d (.product 6)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 6
  · change constraintValue q12Primes d (.product 7)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 7
  · change constraintValue q12Primes d (.product 8)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 8
  · change constraintValue q12Primes d (.product 9)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 9
  · change constraintValue q12Primes d (.product 10)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 10
  · change constraintValue q12Primes d (.product 11)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 11
  · change constraintValue q12Primes d (.product 12)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 12
  · change constraintValue q12Primes d (.product 13)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 13
  · change constraintValue q12Primes d (.product 14)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 14
  · change constraintValue q12Primes d (.product 15)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 15
  · change constraintValue q12Primes d (.product 16)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 16
  · change constraintValue q12Primes d (.product 17)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 17
  · change constraintValue q12Primes d (.product 18)=0
    exact product_constraint_of_mem q12Primes q12Primes_prime d (r2 2) (r3 2) hd 18
  · change constraintValue q12Primes d (.zero 0 8)=0
    let : Fact (q12Primes 8).Prime := ⟨q12Primes_prime 8⟩
    apply first_nonsquare_zero q12Primes 8 d (r2 2) (r3 2) 127451253988476673674 hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · norm_num [r2,r3,D,A,B,q12Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q12Primes 8) (r3 2)).mpr hsq
      exact (by decide +kernel : modularParity (q12Primes 8) (r3 2)≠0) he
  · change constraintValue q12Primes d (.character 2 9 ![0,0,0])=0
    let : Fact (q12Primes 9).Prime := ⟨q12Primes_prime 9⟩
    apply first_square_character q12Primes 9 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 9) (r3 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 11)=0
    let : Fact (q12Primes 11).Prime := ⟨q12Primes_prime 11⟩
    apply first_nonsquare_zero q12Primes 11 d (r2 2) (r3 2) 9786865054420693914 hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · norm_num [r2,r3,D,A,B,q12Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q12Primes 11) (r3 2)).mpr hsq
      exact (by decide +kernel : modularParity (q12Primes 11) (r3 2)≠0) he
  · change constraintValue q12Primes d (.character 2 15 ![0,0,0])=0
    let : Fact (q12Primes 15).Prime := ⟨q12Primes_prime 15⟩
    apply first_square_character q12Primes 15 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 15) (r3 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 2)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 3)=0
    let : Fact (q12Primes 3).Prime := ⟨q12Primes_prime 3⟩
    apply third_nonsquare_zero q12Primes 3 d (r2 2) (r3 2) 416833026272625974154 hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · norm_num [r2,r3,D,A,B,q12Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q12Primes 3) (r2 2)).mpr hsq
      exact (by decide +kernel : modularParity (q12Primes 3) (r2 2)≠0) he
  · change constraintValue q12Primes d (.character 1 4 ![0,0,0])=0
    let : Fact (q12Primes 4).Prime := ⟨q12Primes_prime 4⟩
    apply third_square_character q12Primes 4 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 4) (r2 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.character 1 5 ![0,0,0])=0
    let : Fact (q12Primes 5).Prime := ⟨q12Primes_prime 5⟩
    apply third_square_character q12Primes 5 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 5) (r2 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.zero 0 6)=0
    let : Fact (q12Primes 6).Prime := ⟨q12Primes_prime 6⟩
    apply third_nonsquare_zero q12Primes 6 d (r2 2) (r3 2) 70674111720964265514 hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · norm_num [r2,r3,D,A,B,q12Primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (q12Primes 6) (r2 2)).mpr hsq
      exact (by decide +kernel : modularParity (q12Primes 6) (r2 2)≠0) he
  · change constraintValue q12Primes d (.character 1 7 ![0,0,0])=0
    let : Fact (q12Primes 7).Prime := ⟨q12Primes_prime 7⟩
    apply third_square_character q12Primes 7 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 7) (r2 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.character 1 10 ![0,0,0])=0
    let : Fact (q12Primes 10).Prime := ⟨q12Primes_prime 10⟩
    apply third_square_character q12Primes 10 d (r2 2) (r3 2) hd
    · norm_num [r2,r3,D,A,B,q12Primes]
    · exact (modularParity_eq_zero_iff (q12Primes 10) (r2 2)).mp (by decide +kernel)
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 1)
      norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
  · change constraintValue q12Primes d (.character 0 17 ![0,0,0])=0
    let : Fact (q12Primes 17).Prime := ⟨q12Primes_prime 17⟩
    have hv := shared_prime_characters q12Primes 17 d (r2 2) (r3 2) 41798954345879826642 12662627580507546642 hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q12Primes 17) (41798954345879826642*12662627580507546642)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q12Primes 17) (![-(12662627580507546642),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.1
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q12Primes d (.character 1 17 ![0,0,0])=0
    let : Fact (q12Primes 17).Prime := ⟨q12Primes_prime 17⟩
    have hv := shared_prime_characters q12Primes 17 d (r2 2) (r3 2) 41798954345879826642 12662627580507546642 hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q12Primes 17) (41798954345879826642*12662627580507546642)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q12Primes 17) (![41798954345879826642*(41798954345879826642-12662627580507546642),41798954345879826642,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.2
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q12Primes d (.character 0 18 ![0,0,0])=0
    let : Fact (q12Primes 18).Prime := ⟨q12Primes_prime 18⟩
    have hv := shared_prime_characters q12Primes 18 d (r2 2) (r3 2) 9381064889370274158 2841911546870554158 hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q12Primes 18) (9381064889370274158*2841911546870554158)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q12Primes 18) (![-(2841911546870554158),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.1
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q12Primes d (.character 1 18 ![1,1,0])=0
    let : Fact (q12Primes 18).Prime := ⟨q12Primes_prime 18⟩
    have hv := shared_prime_characters q12Primes 18 d (r2 2) (r3 2) 9381064889370274158 2841911546870554158 hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes])
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      ((modularParity_eq_zero_iff (q12Primes 18) (9381064889370274158*2841911546870554158)).mp (by decide +kernel))
    have hw : (fun c : Fin 3 => modularParity (q12Primes 18) (![9381064889370274158*(9381064889370274158-2841911546870554158),9381064889370274158,1] c))=![1,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    have hvalue := hv.2
    rw [hw] at hvalue
    exact hvalue
  · change constraintValue q12Primes d (.character 0 12 ![0,0,0])=0
    let : Fact (q12Primes 12).Prime := ⟨q12Primes_prime 12⟩
    have hv := simple_difference_character q12Primes 12 d (r2 2) (r3 2) hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q12Primes 12) (![1,-r2 2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q12Primes d (.character 0 13 ![0,0,0])=0
    let : Fact (q12Primes 13).Prime := ⟨q12Primes_prime 13⟩
    have hv := simple_difference_character q12Primes 13 d (r2 2) (r3 2) hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q12Primes 13) (![1,-r2 2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q12Primes d (.character 0 14 ![0,0,0])=0
    let : Fact (q12Primes 14).Prime := ⟨q12Primes_prime 14⟩
    have hv := simple_difference_character q12Primes 14 d (r2 2) (r3 2) hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q12Primes 14) (![1,-r2 2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue q12Primes d (.character 0 16 ![0,0,0])=0
    let : Fact (q12Primes 16).Prime := ⟨q12Primes_prime 16⟩
    have hv := simple_difference_character q12Primes 16 d (r2 2) (r3 2) hd
      (by norm_num [r2,r3,D,A,B,q12Primes]) (by norm_num [r2,r3,D,A,B,q12Primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d (r2 2) (r3 2) hd 0)
        norm_num [coefficient,rootProduct,r2,r3,D,A,B,q12Primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (q12Primes 16) (![1,-r2 2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv

end Z2Z4Rank6.TwistSelmer
