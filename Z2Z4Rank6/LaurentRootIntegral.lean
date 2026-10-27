import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.Linarith

/-!
# Integral Laurent roots and prescribed-constant uniqueness

Power-series rings over fields are integrally closed. Thus a Laurent element
whose positive power is a power series is itself a power series. The square
case is used for rational places of the quadratic root fields.
-/
namespace Z2Z4Rank6
noncomputable section

 theorem exists_powerSeries_of_square {F : Type*} [Field F]
    (z : LaurentSeries F) (f : PowerSeries F)
    (h : z^2=algebraMap (PowerSeries F) (LaurentSeries F) f) :
    ∃r : PowerSeries F,algebraMap (PowerSeries F) (LaurentSeries F) r=z := by
  have hint : IsIntegral (PowerSeries F) (z^2) := by
    rw [h]
    exact isIntegral_algebraMap
  exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=PowerSeries F) (by decide : 0<(2:ℕ)) hint

theorem powerSeries_square_root_unique (a b : PowerSeries ℚ) (h : a^2=b^2)
    (hc : PowerSeries.constantCoeff a=PowerSeries.constantCoeff b)
    (hb : PowerSeries.constantCoeff b≠0) : a=b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with he | he
  · exact he
  · have hm := congrArg PowerSeries.constantCoeff he
    rw [map_neg] at hm
    exact (hb (by linarith)).elim

end
end Z2Z4Rank6
