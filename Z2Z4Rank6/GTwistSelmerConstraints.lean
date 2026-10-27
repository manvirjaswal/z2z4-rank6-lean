import Z2Z4Rank6.GTwistSelmerRowCheck00
import Z2Z4Rank6.GTwistSelmerRowCheck01
import Z2Z4Rank6.GTwistSelmerRowCheck02
import Z2Z4Rank6.GTwistSelmerRowCheck03
import Z2Z4Rank6.GTwistSelmerRowCheck04
import Z2Z4Rank6.GTwistSelmerRowCheck05
import Z2Z4Rank6.GTwistSelmerRowCheck06
import Z2Z4Rank6.GTwistSelmerNecessary

/-! The h constraint matrix annihilates every
canonical everywhere locally soluble covering's bit vector.
Source: Jaswal Proposition 7.2(b), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.GTwistSelmer

open TwistSelmer

theorem hConstraintRow_eq (i : Fin 50) :
    hConstraints i=constraintRow hPrimes (hPrimeConstraints i) := by
  have hfast : ∀ j : Fin 55,
      hConstraints i j=constraintEntry hPrimes (hPrimeConstraints i) j := by
    intro j
    fin_cases i
    · exact hRowCheck00 0 j
    · exact hRowCheck00 1 j
    · exact hRowCheck00 2 j
    · exact hRowCheck00 3 j
    · exact hRowCheck00 4 j
    · exact hRowCheck00 5 j
    · exact hRowCheck00 6 j
    · exact hRowCheck00 7 j
    · exact hRowCheck01 0 j
    · exact hRowCheck01 1 j
    · exact hRowCheck01 2 j
    · exact hRowCheck01 3 j
    · exact hRowCheck01 4 j
    · exact hRowCheck01 5 j
    · exact hRowCheck01 6 j
    · exact hRowCheck01 7 j
    · exact hRowCheck02 0 j
    · exact hRowCheck02 1 j
    · exact hRowCheck02 2 j
    · exact hRowCheck02 3 j
    · exact hRowCheck02 4 j
    · exact hRowCheck02 5 j
    · exact hRowCheck02 6 j
    · exact hRowCheck02 7 j
    · exact hRowCheck03 0 j
    · exact hRowCheck03 1 j
    · exact hRowCheck03 2 j
    · exact hRowCheck03 3 j
    · exact hRowCheck03 4 j
    · exact hRowCheck03 5 j
    · exact hRowCheck03 6 j
    · exact hRowCheck03 7 j
    · exact hRowCheck04 0 j
    · exact hRowCheck04 1 j
    · exact hRowCheck04 2 j
    · exact hRowCheck04 3 j
    · exact hRowCheck04 4 j
    · exact hRowCheck04 5 j
    · exact hRowCheck04 6 j
    · exact hRowCheck04 7 j
    · exact hRowCheck05 0 j
    · exact hRowCheck05 1 j
    · exact hRowCheck05 2 j
    · exact hRowCheck05 3 j
    · exact hRowCheck05 4 j
    · exact hRowCheck05 5 j
    · exact hRowCheck05 6 j
    · exact hRowCheck05 7 j
    · exact hRowCheck06 0 j
    · exact hRowCheck06 1 j
  exact (funext hfast).trans (constraintRow_eq_constraintEntry hPrimes (hPrimeConstraints i)).symm

/-- Covering membership implies the exact generated matrix kernel
condition. -/
theorem hConstraints_mulVec_zero (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3) :
    hConstraints.mulVec (bitVector hPrimes d)=0 := by
  ext i
  change hConstraints i ⬝ᵥ bitVector hPrimes d=0
  rw [hConstraintRow_eq,hConstraint_source d hd i,hConstraintValue_zero d hd i]

end Z2Z4Rank6.GTwistSelmer
