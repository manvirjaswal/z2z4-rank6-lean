module

public import Z2Z4Rank6.GReductionData
public import Z2Z4Rank6.Independence
public import Common.Elliptic.WeierstrassCoordinates

@[expose] public section

/-!
# Kernel checks for the five reductions in Proposition 7.2(b)

Source: Manvir Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117, Proposition 7.2(b).
The coordinate computations are linked to Mathlib's group law by
`Common.WeierstrassCoordinates.encode_nsmul`.
-/

namespace Z2Z4Rank6
namespace GReductionData

open Common.WeierstrassCoordinates

instance primeFact (i : Fin 5) : Fact (Nat.Prime (primes i)) := by
  constructor
  fin_cases i <;> decide +kernel

/-- The reduction of the printed integral model E0 at the selected prime. -/
def curve (i : Fin 5) : WeierstrassCurve (ZMod (primes i)) :=
  E (a0 : ZMod (primes i)) (b0 : ZMod (primes i))

instance curveElliptic (i : Fin 5) : (curve i).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero]
  fin_cases i <;> decide +kernel

/-- The affine reduced coordinate pair from the signed printed formulas. -/
def reducedPoint (i j : Fin 5) : (curve i).toAffine.Point :=
  .mk (x := (reducedX i j : ZMod (primes i)))
    (y := (reducedY i j : ZMod (primes i))) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases i <;> fin_cases j <;> decide +kernel)

/-- A choice of sign of the order-three generator which gives printed M. -/
def generator (i : Fin 5) : (curve i).toAffine.Point :=
  .mk (x := (generatorX i : ZMod (primes i)))
    (y := (generatorY i : ZMod (primes i))) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases i <;> decide +kernel)

/-- The determinant printed in Proposition 7.2(b) is 1 modulo 3. -/
theorem printedMatrix_det : printedMatrix.det = 1 := by
  decide +kernel

/-- The printed matrix is invertible over F3. -/
theorem printedMatrix_isUnit : IsUnit printedMatrix := by
  rw [Matrix.isUnit_iff_isUnit_det, printedMatrix_det]
  decide +kernel

/-- The canonical smaller-y generator convention changes only row
signs of the printed matrix. All column signs equal 1. -/
theorem signedMatrix_bridge (i j : Fin 5) :
    signedMatrix i j = rowSigns i * printedMatrix i j * columnSigns j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- Each displayed generator has exact order three in the
finite-field elliptic curve group. -/
theorem generator_order (i : Fin 5) : addOrderOf (generator i) = 3 := by
  apply addOrderOf_eq_prime_iff.mpr
  constructor
  · apply encode_injective (curve i)
    rw [encode_nsmul]
    change coordinateMul (curve i) 3
      (some ((generatorX i : ZMod (primes i)), (generatorY i : ZMod (primes i)))) = none
    fin_cases i <;> decide +kernel
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- Multiplying each reduced signed point by the displayed group
order divided by three gives exactly the corresponding entry of printed M
as a multiple of the chosen order-three generator. -/
theorem scalar_images (i j : Fin 5) :
    multipliers i • reducedPoint i j = (printedMatrix i j).val • generator i := by
  apply encode_injective (curve i)
  rw [encode_nsmul, encode_nsmul]
  change coordinateMul (curve i) (multipliers i)
      (some ((reducedX i j : ZMod (primes i)), (reducedY i j : ZMod (primes i)))) =
    coordinateMul (curve i) (printedMatrix i j).val
      (some ((generatorX i : ZMod (primes i)), (generatorY i : ZMod (primes i))))
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- All five displayed scalar multipliers are divisible by 4. -/
theorem four_dvd_multiplier (i : Fin 5) : 4 ∣ multipliers i := by
  fin_cases i <;> decide +kernel

/-- The canonical smaller-y generators used to report the row-sign bridge. -/
def canonicalGenerator (i : Fin 5) : (curve i).toAffine.Point :=
  .mk (x := (canonicalGeneratorX i : ZMod (primes i)))
    (y := (canonicalGeneratorY i : ZMod (primes i))) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases i <;> decide +kernel)

/-- The reported row sign changes are generator sign changes. -/
theorem generator_sign_bridge (i : Fin 5) :
    generator i = (rowSigns i).val • canonicalGenerator i := by
  apply encode_injective (curve i)
  rw [encode_nsmul]
  change some ((generatorX i : ZMod (primes i)),(generatorY i : ZMod (primes i))) =
    coordinateMul (curve i) (rowSigns i).val
      (some ((canonicalGeneratorX i : ZMod (primes i)),
        (canonicalGeneratorY i : ZMod (primes i))))
  fin_cases i <;> decide +kernel

/-- All five finite point groups have exactly their printed orders. The 72
orders have a 9-primary factor; no assertion excluding it is made here. -/
theorem curve_card (i : Fin 5) : Nat.card (curve i).toAffine.Point=orders i := by
  have : (longModel ((a0 : ZMod (primes i))^2+(b0 : ZMod (primes i))^2)
      ((a0 : ZMod (primes i))^2*(b0 : ZMod (primes i))^2) 0).IsElliptic :=
    curveElliptic i
  change Nat.card (longModel ((a0 : ZMod (primes i))^2+(b0 : ZMod (primes i))^2)
    ((a0 : ZMod (primes i))^2*(b0 : ZMod (primes i))^2) 0).Point=orders i
  rw [card_point_long_linear]
  · fin_cases i <;> decide +kernel
  · rw [ZMod.ringChar_zmod_n]
    fin_cases i <;> decide +kernel

theorem multiplier_eq_card_div_three (i : Fin 5) :
    multipliers i=Nat.card (curve i).toAffine.Point/3 := by
  rw [curve_card]
  fin_cases i <;> decide +kernel

end GReductionData
end Z2Z4Rank6
