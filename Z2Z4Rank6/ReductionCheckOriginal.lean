import Z2Z4Rank6.ReductionCheckRational

/-!
# The printed mod-3 certificate on the original fiber

Proposition 5.1 of Manvir Jaswal, DOI 10.5281/zenodo.23437117,
scales the original fiber X at c0 to E0. Here the same scalar-image equations
are also checked directly on the original finite-field equations. The generator coordinates are
explicitly inverse-scaled from E0, and all rational scale identities are
proved in ReductionCheckRational.
-/

namespace Z2Z4Rank6.ReductionData

open Common.WeierstrassCoordinates

/-- The printed m0, reduced through its unit denominator. -/
def localM (i : Fin 6) : ZMod (primes i) := 7401 / 2399
/-- The printed u0, reduced through its unit denominator. -/
def localU (i : Fin 6) : ZMod (primes i) := 88235 / 2399
/-- The printed v0, reduced through its unit denominator. -/
def localV (i : Fin 6) : ZMod (primes i) := 86835 / 2399
/-- The scaling ν from the paper, reduced at a good prime. -/
def localScale (i : Fin 6) : ZMod (primes i) := 2399^4 / 1234800

/-- The original family reduced at c0. -/
def originalCurve (i : Fin 6) : WeierstrassCurve (ZMod (primes i)) := X (localM i)

instance originalCurveElliptic (i : Fin 6) : (originalCurve i).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  fin_cases i <;> decide +kernel

/-- The original six sections reduced at the printed base point. -/
def originalPoint (i j : Fin 6) : (originalCurve i).toAffine.Point :=
  .mk (x := sixX (localM i) j) (y := sixY (localM i) (localU i) (localV i) j) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases i <;> fin_cases j <;> decide +kernel)

/-- The order-three generator transported by the printed inverse scaling. -/
def originalGenerator (i : Fin 6) : (originalCurve i).toAffine.Point :=
  .mk (x := (generatorX i : ZMod (primes i)) / localScale i ^ 2)
    (y := (generatorY i : ZMod (primes i)) / localScale i ^ 3) (by
      rw [WeierstrassCurve.Affine.equation_iff]
      fin_cases i <;> decide +kernel)

/-- ν is a unit at all six primes and scales the parameters to a0,b0. -/
theorem local_scale_parameters (i : Fin 6) :
    localScale i ≠ 0 ∧ localScale i * a (localM i) = (a0 : ZMod (primes i)) ∧
      localScale i * b (localM i) = (b0 : ZMod (primes i)) := by
  fin_cases i <;> decide +kernel

/-- All coordinates of the finite reductions satisfy the same printed
scaling relation as the rational points. -/
theorem local_scale_points (i j : Fin 6) :
    localScale i ^ 2 * sixX (localM i) j = (reducedX i j : ZMod (primes i)) ∧
    localScale i ^ 3 * sixY (localM i) (localU i) (localV i) j =
      (reducedY i j : ZMod (primes i)) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Each inverse-scaled generator has exact order three in the
point group of the original fiber. -/
theorem originalGenerator_order (i : Fin 6) : addOrderOf (originalGenerator i) = 3 := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply encode_injective (originalCurve i)
    rw [encode_nsmul]
    change coordinateMul (originalCurve i) 3
      (some (((generatorX i : ZMod (primes i)) / localScale i ^ 2),
        ((generatorY i : ZMod (primes i)) / localScale i ^ 3))) = none
    fin_cases i <;> decide +kernel
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The original sections give exactly the printed matrix M under the
six multiplied good-reduction maps. These are Point-group equalities. -/
theorem original_scalar_images (i j : Fin 6) :
    multipliers i • originalPoint i j = (printedMatrix i j).val • originalGenerator i := by
  apply encode_injective (originalCurve i)
  rw [encode_nsmul, encode_nsmul]
  change coordinateMul (originalCurve i) (multipliers i)
      (some (sixX (localM i) j, sixY (localM i) (localU i) (localV i) j)) =
    coordinateMul (originalCurve i) (printedMatrix i j).val
      (some (((generatorX i : ZMod (primes i)) / localScale i ^ 2),
        ((generatorY i : ZMod (primes i)) / localScale i ^ 3)))
  fin_cases i <;> fin_cases j <;> decide +kernel

end Z2Z4Rank6.ReductionData
