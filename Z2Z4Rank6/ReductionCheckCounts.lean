module

public import Z2Z4Rank6.ReductionCheck

@[expose] public section

/-!
# Finite-field point counts in Proposition 5.1

The printed orders 24, 48, 48, 96, 96, 96 are checked by one finite-field sum
per prime. `card_point_long_linear` identifies this sum with the cardinality of
the Mathlib elliptic point group. Source: Manvir Jaswal,
DOI 10.5281/zenodo.23437117, Proposition 5.1.
-/

namespace Z2Z4Rank6.ReductionData

open Common.WeierstrassCoordinates

/-- All six finite-field groups have exactly their printed orders. -/
theorem curve_card (i : Fin 6) : Nat.card (curve i).toAffine.Point = orders i := by
  have : (longModel ((a0 : ZMod (primes i))^2 + (b0 : ZMod (primes i))^2)
      ((a0 : ZMod (primes i))^2 * (b0 : ZMod (primes i))^2) 0).IsElliptic :=
    curveElliptic i
  change Nat.card (longModel ((a0 : ZMod (primes i))^2 + (b0 : ZMod (primes i))^2)
    ((a0 : ZMod (primes i))^2 * (b0 : ZMod (primes i))^2) 0).Point = orders i
  rw [card_point_long_linear]
  · fin_cases i <;> decide +kernel
  · rw [ZMod.ringChar_zmod_n]
    fin_cases i <;> decide +kernel

/-- The chosen multipliers are precisely group order divided by 3. -/
theorem multiplier_eq_card_div_three (i : Fin 6) :
    multipliers i = Nat.card (curve i).toAffine.Point / 3 := by
  rw [curve_card]
  fin_cases i <;> decide +kernel

/-- 3 divides each finite-field order and 9 divides none. -/
theorem three_primary_orders (i : Fin 6) :
    3 ∣ Nat.card (curve i).toAffine.Point ∧ ¬ 9 ∣ Nat.card (curve i).toAffine.Point := by
  rw [curve_card]
  fin_cases i <;> decide +kernel

end Z2Z4Rank6.ReductionData
