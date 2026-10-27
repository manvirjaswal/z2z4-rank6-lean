module

public import Z2Z4Rank6.SecondW4Torsion

@[expose] public section

/-! # The good reductions of the rational qA-twist at W=4

These statements retain the rational equation used for the printed
two-descent vectors, before its integral scaling. Its reductions at
7 and 13 are smooth and have exactly 8 and 12 points.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily Common.WeierstrassCoordinates

def rationalReductionCurve (i : Fin 2) : WeierstrassCurve (ZMod (primes i)) :=
  reducedModel (primes i) (twistedF (4 : ℚ) (qA 4))

theorem qA_rational_integral_at (i : Fin 2) :
    IntegralModelAt (primes i) (twistedF (4 : ℚ) (qA 4)) := by
  fin_cases i <;>
    norm_num [IntegralModelAt, IntegralAt, twistedF, qA, U, V, lambda, beta, primes]
  all_goals decide +kernel

instance rational_reduction_elliptic (i : Fin 2) : (rationalReductionCurve i).IsElliptic := by
  constructor
  fin_cases i <;>
    norm_num [rationalReductionCurve, reducedModel, primes, residue,
      twistedF, qA, U, V, lambda, beta,
      WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, isUnit_iff_ne_zero]
  all_goals decide +kernel

theorem qA_rational_reduction_card (i : Fin 2) :
    Nat.card (rationalReductionCurve i).toAffine.Point = (![8, 12] : Fin 2 → ℕ) i := by
  have h : rationalReductionCurve i =
      PointScaling.curve (residue (primes i) ((qA (4 : ℚ))*U 4))
        (residue (primes i) ((qA (4 : ℚ))^2*(V 4)^2)) := by
    ext <;> simp [rationalReductionCurve, reducedModel, twistedF, PointScaling.curve]
  rw [h]
  have hE : (PointScaling.curve (residue (primes i) ((qA (4 : ℚ))*U 4))
        (residue (primes i) ((qA (4 : ℚ))^2*(V 4)^2))).IsElliptic :=
    h ▸ rational_reduction_elliptic i
  let : (longModel (residue (primes i) ((qA (4 : ℚ))*U 4))
        (residue (primes i) ((qA (4 : ℚ))^2*(V 4)^2)) 0).IsElliptic := hE
  change Nat.card (longModel _ _ 0).Point = _
  rw [card_point_long_linear]
  · fin_cases i <;> decide +kernel
  · rw [ZMod.ringChar_zmod_n]
    fin_cases i <;> decide

end
end Z2Z4Rank6.SecondW4
