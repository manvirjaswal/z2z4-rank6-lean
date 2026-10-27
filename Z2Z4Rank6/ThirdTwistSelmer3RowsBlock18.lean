import Z2Z4Rank6.ThirdTwistSelmer3Data
import Z2Z4Rank6.TwistSelmerConstraintEntry

/-! Exact certificate for the third-twist paragraph after Proposition 7.2,
Jaswal, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Selmer3
open Z2Z4Rank6.TwistSelmer
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem rowsBlock18_part00 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨0+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part01 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨4+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part02 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨8+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part03 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨12+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part04 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨16+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part05 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨20+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part06 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨24+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part07 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨28+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part08 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨32+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part09 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨36+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part10 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨40+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part11 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨44+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part12 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨48+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part13 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨52+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part14 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 4,let c : Fin 61 := ⟨56+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18_part15 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 1,let c : Fin 61 := ⟨60+j.val,by omega⟩
      constraints i c=TwistSelmer.constraintEntry primes (primeConstraints i) c := by
  decide +kernel
theorem rowsBlock18 : ∀ k : Fin 1,
    let i : Fin 57 := ⟨54+k.val,by omega⟩
    ∀ j : Fin 61,constraints i j=TwistSelmer.constraintEntry primes (primeConstraints i) j := by
  intro k
  dsimp only
  intro j
  fin_cases j
  · exact rowsBlock18_part00 k 0
  · exact rowsBlock18_part00 k 1
  · exact rowsBlock18_part00 k 2
  · exact rowsBlock18_part00 k 3
  · exact rowsBlock18_part01 k 0
  · exact rowsBlock18_part01 k 1
  · exact rowsBlock18_part01 k 2
  · exact rowsBlock18_part01 k 3
  · exact rowsBlock18_part02 k 0
  · exact rowsBlock18_part02 k 1
  · exact rowsBlock18_part02 k 2
  · exact rowsBlock18_part02 k 3
  · exact rowsBlock18_part03 k 0
  · exact rowsBlock18_part03 k 1
  · exact rowsBlock18_part03 k 2
  · exact rowsBlock18_part03 k 3
  · exact rowsBlock18_part04 k 0
  · exact rowsBlock18_part04 k 1
  · exact rowsBlock18_part04 k 2
  · exact rowsBlock18_part04 k 3
  · exact rowsBlock18_part05 k 0
  · exact rowsBlock18_part05 k 1
  · exact rowsBlock18_part05 k 2
  · exact rowsBlock18_part05 k 3
  · exact rowsBlock18_part06 k 0
  · exact rowsBlock18_part06 k 1
  · exact rowsBlock18_part06 k 2
  · exact rowsBlock18_part06 k 3
  · exact rowsBlock18_part07 k 0
  · exact rowsBlock18_part07 k 1
  · exact rowsBlock18_part07 k 2
  · exact rowsBlock18_part07 k 3
  · exact rowsBlock18_part08 k 0
  · exact rowsBlock18_part08 k 1
  · exact rowsBlock18_part08 k 2
  · exact rowsBlock18_part08 k 3
  · exact rowsBlock18_part09 k 0
  · exact rowsBlock18_part09 k 1
  · exact rowsBlock18_part09 k 2
  · exact rowsBlock18_part09 k 3
  · exact rowsBlock18_part10 k 0
  · exact rowsBlock18_part10 k 1
  · exact rowsBlock18_part10 k 2
  · exact rowsBlock18_part10 k 3
  · exact rowsBlock18_part11 k 0
  · exact rowsBlock18_part11 k 1
  · exact rowsBlock18_part11 k 2
  · exact rowsBlock18_part11 k 3
  · exact rowsBlock18_part12 k 0
  · exact rowsBlock18_part12 k 1
  · exact rowsBlock18_part12 k 2
  · exact rowsBlock18_part12 k 3
  · exact rowsBlock18_part13 k 0
  · exact rowsBlock18_part13 k 1
  · exact rowsBlock18_part13 k 2
  · exact rowsBlock18_part13 k 3
  · exact rowsBlock18_part14 k 0
  · exact rowsBlock18_part14 k 1
  · exact rowsBlock18_part14 k 2
  · exact rowsBlock18_part14 k 3
  · exact rowsBlock18_part15 k 0

end Z2Z4Rank6.ThirdTwist.Selmer3
