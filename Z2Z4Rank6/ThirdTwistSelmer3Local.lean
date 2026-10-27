import Z2Z4Rank6.ThirdTwistSelmer3Data

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem constraints_satisfied (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (i : Fin 57) : constraintValue primes d (primeConstraints i)=0 := by
  fin_cases i
  · change constraintValue primes d (.zero 0 2)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 3)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 6)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 13)=0
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
  · change constraintValue primes d (.zero 0 19)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 1)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 4)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 5)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 8)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 1 15)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 7)=0
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
  · change constraintValue primes d (.zero 2 11)=0
    apply zero_constraint_of_nondiv
    intro ht
    have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
    norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
      ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 2 14)=0
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
  · change constraintValue primes d (.product 18)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 18
  · change constraintValue primes d (.product 19)=0
    exact product_constraint_of_mem primes primes_prime d r2 r3 hd 19
  · change constraintValue primes d (.character 2 7 ![0,0,0])=0
    let : Fact (primes 7).Prime := ⟨primes_prime 7⟩
    apply first_square_character primes 7 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(14 : ZMod (primes 7)),?_⟩
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
    · refine ⟨(2 : ZMod (primes 10)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 11)=0
    let : Fact (primes 11).Prime := ⟨primes_prime 11⟩
    apply first_nonsquare_zero primes 11 d r2 r3 3542407864064386094258386 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 11) r3).mpr hsq
      exact (by decide +kernel : modularParity (primes 11) r3≠0) he
  · change constraintValue primes d (.zero 0 14)=0
    let : Fact (primes 14).Prime := ⟨primes_prime 14⟩
    apply first_nonsquare_zero primes 14 d r2 r3 100540953092143196123074 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 2)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 14) r3).mpr hsq
      exact (by decide +kernel : modularParity (primes 14) r3≠0) he
  · change constraintValue primes d (.character 1 1 ![0,0,0])=0
    let : Fact (primes 1).Prime := ⟨primes_prime 1⟩
    apply third_square_character primes 1 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(1 : ZMod (primes 1)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.character 1 4 ![0,0,0])=0
    let : Fact (primes 4).Prime := ⟨primes_prime 4⟩
    apply third_square_character primes 4 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(2 : ZMod (primes 4)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.character 1 5 ![0,0,0])=0
    let : Fact (primes 5).Prime := ⟨primes_prime 5⟩
    apply third_square_character primes 5 d r2 r3 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · refine ⟨(6 : ZMod (primes 5)),?_⟩
      decide +kernel +revert
    · decide +kernel +revert
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
  · change constraintValue primes d (.zero 0 8)=0
    let : Fact (primes 8).Prime := ⟨primes_prime 8⟩
    apply third_nonsquare_zero primes 8 d r2 r3 6772879020447312783947586 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 8) r2).mpr hsq
      exact (by decide +kernel : modularParity (primes 8) r2≠0) he
  · change constraintValue primes d (.zero 0 15)=0
    let : Fact (primes 15).Prime := ⟨primes_prime 15⟩
    apply third_nonsquare_zero primes 15 d r2 r3 20847412264629876510546 hd
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]
    · intro ht
      have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 1)
      norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
        ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
    · intro hsq
      have he := (modularParity_eq_zero_iff (primes 15) r2).mpr hsq
      exact (by decide +kernel : modularParity (primes 15) r2≠0) he
  · change constraintValue primes d (.character 0 9 ![0,0,0])=0
    let : Fact (primes 9).Prime := ⟨primes_prime 9⟩
    have hv := shared_prime_characters primes 9 d r2 r3 895475485807424918848593278 242238502837700697655657278 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(465745253341194355551874722),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 9) (![(-(242238502837700697655657278 : ℤ)),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 9 ![1,1,0])=0
    let : Fact (primes 9).Prime := ⟨primes_prime 9⟩
    have hv := shared_prime_characters primes 9 d r2 r3 895475485807424918848593278 242238502837700697655657278 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(465745253341194355551874722),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 9) (![(895475485807424918848593278 : ℤ)*(895475485807424918848593278-242238502837700697655657278),895475485807424918848593278,1] c))=![1,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 12 ![1,0,0])=0
    let : Fact (primes 12).Prime := ⟨primes_prime 12⟩
    have hv := shared_prime_characters primes 12 d r2 r3 185406818647352295973056758 50155108517056972642360758 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(96431836594872840136291242),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 12) (![(-(50155108517056972642360758 : ℤ)),1,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 12 ![1,0,0])=0
    let : Fact (primes 12).Prime := ⟨primes_prime 12⟩
    have hv := shared_prime_characters primes 12 d r2 r3 185406818647352295973056758 50155108517056972642360758 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(96431836594872840136291242),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 12) (![(185406818647352295973056758 : ℤ)*(185406818647352295973056758-50155108517056972642360758),185406818647352295973056758,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 17 ![1,0,0])=0
    let : Fact (primes 17).Prime := ⟨primes_prime 17⟩
    have hv := shared_prime_characters primes 17 d r2 r3 4623459061073159528274622 1250709615881789826410622 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(2404704702519623718657378),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 17) (![(-(1250709615881789826410622 : ℤ)),1,1] c))=![1,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 17 ![0,0,0])=0
    let : Fact (primes 17).Prime := ⟨primes_prime 17⟩
    have hv := shared_prime_characters primes 17 d r2 r3 4623459061073159528274622 1250709615881789826410622 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(2404704702519623718657378),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 17) (![(4623459061073159528274622 : ℤ)*(4623459061073159528274622-1250709615881789826410622),4623459061073159528274622,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 18 ![0,0,0])=0
    let : Fact (primes 18).Prime := ⟨primes_prime 18⟩
    have hv := shared_prime_characters primes 18 d r2 r3 2607803942806181993053094 705447031003899423125094 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(1356343447985385383910906),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 18) (![(-(705447031003899423125094 : ℤ)),1,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue primes d (.character 1 18 ![0,1,0])=0
    let : Fact (primes 18).Prime := ⟨primes_prime 18⟩
    have hv := shared_prime_characters primes 18 d r2 r3 2607803942806181993053094 705447031003899423125094 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
      (by decide +kernel +revert) (by decide +kernel +revert) (by decide +kernel +revert)
      (by refine ⟨(1356343447985385383910906),?_⟩; norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes])
    have hw : (fun c : Fin 3 => modularParity (primes 18) (![(2607803942806181993053094 : ℤ)*(2607803942806181993053094-705447031003899423125094),2607803942806181993053094,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue primes d (.character 0 3 ![0,0,0])=0
    let : Fact (primes 3).Prime := ⟨primes_prime 3⟩
    have hv := simple_difference_character primes 3 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 3) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 6 ![0,0,0])=0
    let : Fact (primes 6).Prime := ⟨primes_prime 6⟩
    have hv := simple_difference_character primes 6 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 6) (![1,-r2,1] c))=![0,0,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv
  · change constraintValue primes d (.character 0 13 ![0,1,0])=0
    let : Fact (primes 13).Prime := ⟨primes_prime 13⟩
    have hv := simple_difference_character primes 13 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 13) (![1,-r2,1] c))=![0,1,0] := by
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
  · change constraintValue primes d (.character 0 19 ![0,1,0])=0
    let : Fact (primes 19).Prime := ⟨primes_prime 19⟩
    have hv := simple_difference_character primes 19 d r2 r3 hd
      (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by norm_num [r2,r3,ThirdTwist.r2,ThirdTwist.r3,ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes]) (by decide +kernel +revert)
      (by
        intro ht
        have hh := ht.trans (coefficient_divisor_of_mem d r2 r3 hd 0)
        norm_num [coefficient,rootProduct,r2,r3,ThirdTwist.r2,ThirdTwist.r3,
          ThirdTwist.D,ThirdTwist.A,ThirdTwist.B,primes] at hh
)
    have hw : (fun c : Fin 3 => modularParity (primes 19) (![1,-r2,1] c))=![0,1,0] := by
      funext c
      fin_cases c <;> decide +kernel +revert
    rw [hw] at hv
    exact hv

end Z2Z4Rank6.ThirdTwist.Selmer3
