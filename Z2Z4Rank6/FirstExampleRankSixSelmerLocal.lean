import Z2Z4Rank6.FirstExampleRankSixSelmerData

namespace Z2Z4Rank6.FirstExampleRankSix.Selmer
open Z2Z4Rank6.TwistSelmer
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
theorem constraints_satisfied (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) (i : Fin 70) :
    constraintValue primes d (primeConstraints i)=0 := by
  fin_cases i
  · change constraintValue primes d (.zero 0 1)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 7)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 14)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 18)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 19)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 20)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 21)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 22)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 0 23)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 9)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 10)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 13)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 1 16)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 0)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 2)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 11)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 12)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 15)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.zero 2 17)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.product 0)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 0
  · change constraintValue primes d (.product 1)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 1
  · change constraintValue primes d (.product 2)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 2
  · change constraintValue primes d (.product 3)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 3
  · change constraintValue primes d (.product 4)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 4
  · change constraintValue primes d (.product 5)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 5
  · change constraintValue primes d (.product 6)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 6
  · change constraintValue primes d (.product 7)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 7
  · change constraintValue primes d (.product 8)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 8
  · change constraintValue primes d (.product 9)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 9
  · change constraintValue primes d (.product 10)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 10
  · change constraintValue primes d (.product 11)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 11
  · change constraintValue primes d (.product 12)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 12
  · change constraintValue primes d (.product 13)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 13
  · change constraintValue primes d (.product 14)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 14
  · change constraintValue primes d (.product 15)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 15
  · change constraintValue primes d (.product 16)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 16
  · change constraintValue primes d (.product 17)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 17
  · change constraintValue primes d (.product 18)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 18
  · change constraintValue primes d (.product 19)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 19
  · change constraintValue primes d (.product 20)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 20
  · change constraintValue primes d (.product 21)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 21
  · change constraintValue primes d (.product 22)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 22
  · change constraintValue primes d (.product 23)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 23
  · change constraintValue primes d (.character 2 2 ![0,0,0])=0
    let : Fact (primes 2).Prime := ⟨primes_prime 2⟩
    apply first_square_character primes 2 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 2)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 2 5 ![0,0,0])=0
    let : Fact (primes 5).Prime := ⟨primes_prime 5⟩
    apply first_square_character primes 5 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 5)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 2 11 ![0,0,0])=0
    let : Fact (primes 11).Prime := ⟨primes_prime 11⟩
    apply first_square_character primes 11 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 11)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 2 12 ![0,0,0])=0
    let : Fact (primes 12).Prime := ⟨primes_prime 12⟩
    apply first_square_character primes 12 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 12)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 2 15 ![0,0,0])=0
    let : Fact (primes 15).Prime := ⟨primes_prime 15⟩
    apply first_square_character primes 15 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 15)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 2 17 ![0,0,0])=0
    let : Fact (primes 17).Prime := ⟨primes_prime 17⟩
    apply first_square_character primes 17 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(3329722383911 : ZMod (primes 17)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 3 ![0,0,0])=0
    let : Fact (primes 3).Prime := ⟨primes_prime 3⟩
    apply third_square_character primes 3 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 3)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 4 ![0,0,0])=0
    let : Fact (primes 4).Prime := ⟨primes_prime 4⟩
    apply third_square_character primes 4 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 4)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 6 ![0,0,0])=0
    let : Fact (primes 6).Prime := ⟨primes_prime 6⟩
    apply third_square_character primes 6 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 6)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 8 ![0,0,0])=0
    let : Fact (primes 8).Prime := ⟨primes_prime 8⟩
    apply third_square_character primes 8 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 8)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 9 ![0,0,0])=0
    let : Fact (primes 9).Prime := ⟨primes_prime 9⟩
    apply third_square_character primes 9 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 9)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 10 ![0,0,0])=0
    let : Fact (primes 10).Prime := ⟨primes_prime 10⟩
    apply third_square_character primes 10 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 10)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 13 ![0,0,0])=0
    let : Fact (primes 13).Prime := ⟨primes_prime 13⟩
    apply third_square_character primes 13 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 13)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 1 16 ![0,0,0])=0
    let : Fact (primes 16).Prime := ⟨primes_prime 16⟩
    apply third_square_character primes 16 d r2 r3 hd
    · norm_num [r2,r3,primes]
    · refine ⟨(7037226227200 : ZMod (primes 16)),?_⟩
      norm_num [r2,r3,primes]
    · decide +kernel
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,primes] at hh
  · change constraintValue primes d (.character 0 1 ![0,1,0])=0
    let : Fact (primes 1).Prime := ⟨primes_prime 1⟩
    have hv := simple_difference_character primes 1 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 1) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 7 ![0,1,0])=0
    let : Fact (primes 7).Prime := ⟨primes_prime 7⟩
    have hv := simple_difference_character primes 7 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 7) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 14 ![0,1,0])=0
    let : Fact (primes 14).Prime := ⟨primes_prime 14⟩
    have hv := simple_difference_character primes 14 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 14) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 18 ![0,0,0])=0
    let : Fact (primes 18).Prime := ⟨primes_prime 18⟩
    have hv := simple_difference_character primes 18 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 18) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 19 ![0,0,0])=0
    let : Fact (primes 19).Prime := ⟨primes_prime 19⟩
    have hv := simple_difference_character primes 19 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 19) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 20 ![0,0,0])=0
    let : Fact (primes 20).Prime := ⟨primes_prime 20⟩
    have hv := simple_difference_character primes 20 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 20) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 21 ![0,1,0])=0
    let : Fact (primes 21).Prime := ⟨primes_prime 21⟩
    have hv := simple_difference_character primes 21 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 21) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 22 ![0,1,0])=0
    let : Fact (primes 22).Prime := ⟨primes_prime 22⟩
    have hv := simple_difference_character primes 22 d r2 r3 hd
      (by norm_num [r2,r3,primes]) (by norm_num [r2,r3,primes]) (by decide +kernel)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 22) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel
    rw [hw] at hv
    exact hv
end Z2Z4Rank6.FirstExampleRankSix.Selmer
