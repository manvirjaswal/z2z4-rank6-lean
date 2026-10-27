import Z2Z4Rank6.ThirdTwistSelmer2Data

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer2
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem constraints_satisfied (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (i : Fin 53) : constraintValue primes d (primeConstraints i)=0 := by
  fin_cases i
  · change constraintValue primes d (.zero 0 0)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 1)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 7)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 12)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 16)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 17)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 2)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 9)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 14)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 10)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
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
  · change constraintValue primes d (.zero 0 3)=0
    let : Fact (primes 3).Prime := ⟨primes_prime 3⟩
    apply first_nonsquare_zero primes 3 d r2 r3 2448262985889421987 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 3) r3).mpr hsq
      exact (by decide +kernel : modularParity (primes 3) r3≠0) he
  · change constraintValue primes d (.character 2 4 ![0,0,0])=0
    let : Fact (primes 4).Prime := ⟨primes_prime 4⟩
    apply first_square_character primes 4 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(1 : ZMod (primes 4)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 5)=0
    let : Fact (primes 5).Prime := ⟨primes_prime 5⟩
    apply first_nonsquare_zero primes 5 d r2 r3 709851398275631227 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 5) r3).mpr hsq
      exact (by decide +kernel : modularParity (primes 5) r3≠0) he
  · change constraintValue primes d (.character 2 8 ![0,0,0])=0
    let : Fact (primes 8).Prime := ⟨primes_prime 8⟩
    apply first_square_character primes 8 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(13 : ZMod (primes 8)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.character 2 10 ![0,0,0])=0
    let : Fact (primes 10).Prime := ⟨primes_prime 10⟩
    apply first_square_character primes 10 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(22 : ZMod (primes 10)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 2)=0
    let : Fact (primes 2).Prime := ⟨primes_prime 2⟩
    apply third_nonsquare_zero primes 2 d r2 r3 1518095949030267787 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 2) r2).mpr hsq
      exact (by decide +kernel : modularParity (primes 2) r2≠0) he
  · change constraintValue primes d (.zero 0 6)=0
    let : Fact (primes 6).Prime := ⟨primes_prime 6⟩
    apply third_nonsquare_zero primes 6 d r2 r3 131323178981857075 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 6) r2).mpr hsq
      exact (by decide +kernel : modularParity (primes 6) r2≠0) he
  · change constraintValue primes d (.character 1 9 ![0,0,0])=0
    let : Fact (primes 9).Prime := ⟨primes_prime 9⟩
    apply third_square_character primes 9 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(19 : ZMod (primes 9)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 14)=0
    let : Fact (primes 14).Prime := ⟨primes_prime 14⟩
    apply third_nonsquare_zero primes 14 d r2 r3 664421118778675 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 14) r2).mpr hsq
      exact (by decide +kernel : modularParity (primes 14) r2≠0) he
  · change constraintValue primes d (.character 0 11 ![1,0,0])=0
    let : Fact (primes 11).Prime := ⟨primes_prime 11⟩
    have hv := shared_prime_characters primes 11 d r2 r3 1445360076007008161 457257815972972225 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(812958911415265615),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 11) (![(-(457257815972972225 : ℤ)),1,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 11 ![0,0,0])=0
    let : Fact (primes 11).Prime := ⟨primes_prime 11⟩
    have hv := shared_prime_characters primes 11 d r2 r3 1445360076007008161 457257815972972225 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(812958911415265615),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 11) (![(1445360076007008161 : ℤ)*(1445360076007008161-457257815972972225),1445360076007008161,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 13 ![1,0,0])=0
    let : Fact (primes 13).Prime := ⟨primes_prime 13⟩
    have hv := shared_prime_characters primes 13 d r2 r3 718352612626237589 227259872609321525 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(404045446990820635),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 13) (![(-(227259872609321525 : ℤ)),1,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 13 ![1,0,0])=0
    let : Fact (primes 13).Prime := ⟨primes_prime 13⟩
    have hv := shared_prime_characters primes 13 d r2 r3 718352612626237589 227259872609321525 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(404045446990820635),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 13) (![(718352612626237589 : ℤ)*(718352612626237589-227259872609321525),718352612626237589,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 15 ![0,0,0])=0
    let : Fact (primes 15).Prime := ⟨primes_prime 15⟩
    have hv := shared_prime_characters primes 15 d r2 r3 67282605893764261 21285697546694725 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(37843852858927115),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 15) (![(-(21285697546694725 : ℤ)),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 15 ![1,1,0])=0
    let : Fact (primes 15).Prime := ⟨primes_prime 15⟩
    have hv := shared_prime_characters primes 15 d r2 r3 67282605893764261 21285697546694725 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(37843852858927115),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 15) (![(67282605893764261 : ℤ)*(67282605893764261-21285697546694725),67282605893764261,1] c))=![1,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 1 ![0,1,0])=0
    let : Fact (primes 1).Prime := ⟨primes_prime 1⟩
    have hv := simple_difference_character primes 1 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 1) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 7 ![0,1,0])=0
    let : Fact (primes 7).Prime := ⟨primes_prime 7⟩
    have hv := simple_difference_character primes 7 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 7) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 12 ![0,0,0])=0
    let : Fact (primes 12).Prime := ⟨primes_prime 12⟩
    have hv := simple_difference_character primes 12 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 12) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 16 ![0,1,0])=0
    let : Fact (primes 16).Prime := ⟨primes_prime 16⟩
    have hv := simple_difference_character primes 16 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 16) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 17 ![0,0,0])=0
    let : Fact (primes 17).Prime := ⟨primes_prime 17⟩
    have hv := simple_difference_character primes 17 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 17) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv

end Z2Z4Rank6.ThirdTwist.Selmer2
