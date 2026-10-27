module

public import Z2Z4Rank6.GTwistSelmerRows

@[expose] public section

/-! Canonical covering values satisfy every semantic row for the
extra h-twist. Source: Jaswal Proposition 7.2(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.GTwistSelmer

open scoped BigOperators
open TwistSelmer
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

private def hSupportBlock : Fin 3 → ℤ := ![D*A*B,D*A*(C:ℤ),D*B*(C:ℤ)]

private theorem hSupportDivisor (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (c : Fin 3) : coefficient d c∣hSupportBlock c := by
  have h := supports d hd
  fin_cases c
  · exact h.1
  · exact h.2.1
  · exact h.2.2

private theorem hZeroValue (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (c : Fin 3) (j : Fin 18) (hn : ¬(hPrimes j : ℤ)∣hSupportBlock c) :
    constraintValue hPrimes d (.zero c j)=0 := by
  apply zero_constraint_of_nondiv
  exact fun h => hn (h.trans (hSupportDivisor d hd c))

private theorem hSquareValue (d : ECFullTriple) (c : Fin 3) (j : Fin 18)
    [Fact (hPrimes j).Prime] (hn : ¬(hPrimes j : ℤ)∣coefficient d c)
    (hq : IsSquare ((coefficient d c : ℤ) : ZMod (hPrimes j))) :
    constraintValue hPrimes d (.character c j ![0,0,0])=0 := by
  have h := (modularParity_eq_zero_iff (hPrimes j) (coefficient d c)).mpr hq
  simpa [constraintValue,Fin.sum_univ_succ,SplitTwistPrime.unitPart,hn] using h

/-- Every everywhere locally soluble canonical covering satisfies
all fifty support/product/local-character constraints. -/
theorem hConstraintValue_zero (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (i : Fin 50) : constraintValue hPrimes d (hPrimeConstraints i)=0 := by
  fin_cases i
  · change constraintValue hPrimes d (.zero 0 0)=0
    apply hZeroValue d hd 0 0
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 0 2)=0
    apply hZeroValue d hd 0 2
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 0 3)=0
    apply hZeroValue d hd 0 3
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 0 13)=0
    apply hZeroValue d hd 0 13
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 0 14)=0
    apply hZeroValue d hd 0 14
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 0 16)=0
    apply hZeroValue d hd 0 16
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 1 7)=0
    apply hZeroValue d hd 1 7
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 1 8)=0
    apply hZeroValue d hd 1 8
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 1 10)=0
    apply hZeroValue d hd 1 10
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 1 11)=0
    apply hZeroValue d hd 1 11
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 2 4)=0
    apply hZeroValue d hd 2 4
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 2 5)=0
    apply hZeroValue d hd 2 5
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 2 6)=0
    apply hZeroValue d hd 2 6
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 2 9)=0
    apply hZeroValue d hd 2 9
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.zero 2 12)=0
    apply hZeroValue d hd 2 12
    norm_num [hPrimes,hSupportBlock,D,A,B,C]
  · change constraintValue hPrimes d (.product 0)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 0
  · change constraintValue hPrimes d (.product 1)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 1
  · change constraintValue hPrimes d (.product 2)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 2
  · change constraintValue hPrimes d (.product 3)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 3
  · change constraintValue hPrimes d (.product 4)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 4
  · change constraintValue hPrimes d (.product 5)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 5
  · change constraintValue hPrimes d (.product 6)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 6
  · change constraintValue hPrimes d (.product 7)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 7
  · change constraintValue hPrimes d (.product 8)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 8
  · change constraintValue hPrimes d (.product 9)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 9
  · change constraintValue hPrimes d (.product 10)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 10
  · change constraintValue hPrimes d (.product 11)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 11
  · change constraintValue hPrimes d (.product 12)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 12
  · change constraintValue hPrimes d (.product 13)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 13
  · change constraintValue hPrimes d (.product 14)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 14
  · change constraintValue hPrimes d (.product 15)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 15
  · change constraintValue hPrimes d (.product 16)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 16
  · change constraintValue hPrimes d (.product 17)=0
    exact product_constraint_of_mem hPrimes hPrimes_prime d r2 r3 hd 17
  · change constraintValue hPrimes d (.character 2 4 ![0,0,0])=0
    let : Fact (hPrimes 4).Prime := ⟨hPrimes_prime 4⟩
    apply hSquareValue d 2 4
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 2)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact first_square_condition d hd (hPrimes 4) (by decide +kernel)
  · change constraintValue hPrimes d (.character 2 5 ![0,0,0])=0
    let : Fact (hPrimes 5).Prime := ⟨hPrimes_prime 5⟩
    apply hSquareValue d 2 5
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 2)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact first_square_condition d hd (hPrimes 5) (by decide +kernel)
  · change constraintValue hPrimes d (.character 2 6 ![0,0,0])=0
    let : Fact (hPrimes 6).Prime := ⟨hPrimes_prime 6⟩
    apply hSquareValue d 2 6
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 2)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact first_square_condition d hd (hPrimes 6) (by decide +kernel)
  · change constraintValue hPrimes d (.character 2 9 ![0,0,0])=0
    let : Fact (hPrimes 9).Prime := ⟨hPrimes_prime 9⟩
    apply hSquareValue d 2 9
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 2)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact first_square_condition d hd (hPrimes 9) (by decide +kernel)
  · change constraintValue hPrimes d (.character 2 12 ![0,0,0])=0
    let : Fact (hPrimes 12).Prime := ⟨hPrimes_prime 12⟩
    apply hSquareValue d 2 12
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 2)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact first_square_condition d hd (hPrimes 12) (by decide +kernel)
  · change constraintValue hPrimes d (.character 1 7 ![0,0,0])=0
    let : Fact (hPrimes 7).Prime := ⟨hPrimes_prime 7⟩
    apply hSquareValue d 1 7
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 1)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact second_square_condition d hd (hPrimes 7) (by decide +kernel)
  · change constraintValue hPrimes d (.character 1 8 ![0,0,0])=0
    let : Fact (hPrimes 8).Prime := ⟨hPrimes_prime 8⟩
    apply hSquareValue d 1 8
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 1)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact second_square_condition d hd (hPrimes 8) (by decide +kernel)
  · change constraintValue hPrimes d (.character 1 10 ![0,0,0])=0
    let : Fact (hPrimes 10).Prime := ⟨hPrimes_prime 10⟩
    apply hSquareValue d 1 10
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 1)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact second_square_condition d hd (hPrimes 10) (by decide +kernel)
  · change constraintValue hPrimes d (.character 1 11 ![0,0,0])=0
    let : Fact (hPrimes 11).Prime := ⟨hPrimes_prime 11⟩
    apply hSquareValue d 1 11
    · intro hh
      have ht := hh.trans (hSupportDivisor d hd 1)
      norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht
    · exact second_square_condition d hd (hPrimes 11) (by decide +kernel)
  · change constraintValue hPrimes d (.character 0 15 ![0,0,0])=0
    let : Fact (hPrimes 15).Prime := ⟨hPrimes_prime 15⟩
    have hv := shared_prime_characters hPrimes 15 d r2 r3 (3854670157346283561) (1046293116978699561) hd
      (by norm_num [hPrimes,r2,D,A]) (by norm_num [hPrimes,r3,D,B])
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by refine ⟨(2008261649749508439),?_⟩; norm_num [hPrimes])
    have hw : (fun c : Fin 3 => modularParity (hPrimes 15) (![(-(1046293116978699561 : ℤ)),1,1] c))=![0,0,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue hPrimes d (.character 1 15 ![1,1,0])=0
    let : Fact (hPrimes 15).Prime := ⟨hPrimes_prime 15⟩
    have hv := shared_prime_characters hPrimes 15 d r2 r3 (3854670157346283561) (1046293116978699561) hd
      (by norm_num [hPrimes,r2,D,A]) (by norm_num [hPrimes,r3,D,B])
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by refine ⟨(2008261649749508439),?_⟩; norm_num [hPrimes])
    have hw : (fun c : Fin 3 => modularParity (hPrimes 15) (![(3854670157346283561 : ℤ)*(3854670157346283561-1046293116978699561),3854670157346283561,1] c))=![1,1,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue hPrimes d (.character 0 17 ![1,0,0])=0
    let : Fact (hPrimes 17).Prime := ⟨hPrimes_prime 17⟩
    have hv := shared_prime_characters hPrimes 17 d r2 r3 (2389044250184374497) (648470674037206497) hd
      (by norm_num [hPrimes,r2,D,A]) (by norm_num [hPrimes,r3,D,B])
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by refine ⟨(1244678727713209503),?_⟩; norm_num [hPrimes])
    have hw : (fun c : Fin 3 => modularParity (hPrimes 17) (![(-(648470674037206497 : ℤ)),1,1] c))=![1,0,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.1
  · change constraintValue hPrimes d (.character 1 17 ![0,0,0])=0
    let : Fact (hPrimes 17).Prime := ⟨hPrimes_prime 17⟩
    have hv := shared_prime_characters hPrimes 17 d r2 r3 (2389044250184374497) (648470674037206497) hd
      (by norm_num [hPrimes,r2,D,A]) (by norm_num [hPrimes,r3,D,B])
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by norm_num [hPrimes]; decide +kernel)
      (by refine ⟨(1244678727713209503),?_⟩; norm_num [hPrimes])
    have hw : (fun c : Fin 3 => modularParity (hPrimes 17) (![(2389044250184374497 : ℤ)*(2389044250184374497-648470674037206497),2389044250184374497,1] c))=![0,0,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv.2
  · change constraintValue hPrimes d (.character 0 3 ![0,1,0])=0
    let : Fact (hPrimes 3).Prime := ⟨hPrimes_prime 3⟩
    have hv := simple_difference_character hPrimes 3 d r2 r3 hd
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,D,A]; decide +kernel)
      (by intro hh; have ht := hh.trans (hSupportDivisor d hd 0)
          norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht)
    have hw : (fun c : Fin 3 => modularParity (hPrimes 3) (![1,-r2,1] c))=![0,1,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv
  · change constraintValue hPrimes d (.character 0 13 ![0,0,0])=0
    let : Fact (hPrimes 13).Prime := ⟨hPrimes_prime 13⟩
    have hv := simple_difference_character hPrimes 13 d r2 r3 hd
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,D,A]; decide +kernel)
      (by intro hh; have ht := hh.trans (hSupportDivisor d hd 0)
          norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht)
    have hw : (fun c : Fin 3 => modularParity (hPrimes 13) (![1,-r2,1] c))=![0,0,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv
  · change constraintValue hPrimes d (.character 0 14 ![0,1,0])=0
    let : Fact (hPrimes 14).Prime := ⟨hPrimes_prime 14⟩
    have hv := simple_difference_character hPrimes 14 d r2 r3 hd
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,D,A]; decide +kernel)
      (by intro hh; have ht := hh.trans (hSupportDivisor d hd 0)
          norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht)
    have hw : (fun c : Fin 3 => modularParity (hPrimes 14) (![1,-r2,1] c))=![0,1,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv
  · change constraintValue hPrimes d (.character 0 16 ![0,0,0])=0
    let : Fact (hPrimes 16).Prime := ⟨hPrimes_prime 16⟩
    have hv := simple_difference_character hPrimes 16 d r2 r3 hd
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,r3,D,A,B])
      (by norm_num [hPrimes,r2,D,A]; decide +kernel)
      (by intro hh; have ht := hh.trans (hSupportDivisor d hd 0)
          norm_num [hPrimes,coefficient,hSupportBlock,D,A,B,C] at ht)
    have hw : (fun c : Fin 3 => modularParity (hPrimes 16) (![1,-r2,1] c))=![0,0,0] := by
      ext c
      fin_cases c <;> decide +kernel +revert
    simpa only [hw] using hv

end
end Z2Z4Rank6.GTwistSelmer
