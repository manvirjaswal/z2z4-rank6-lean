module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Algebra.Rat

@[expose] public section

/-!
# Rational nonsquares remain nonsquare in fields with rational Laurent places

Leading coefficients multiply in a Laurent-series field. A square root of a
rational constant would therefore give a rational square root of that constant.
-/
namespace Z2Z4Rank6

theorem not_isSquare_ratCast_of_laurent_embedding {K : Type*} [Field K]
    (f : K→+*LaurentSeries ℚ) (a : ℚ) (ha : ¬IsSquare a) : ¬IsSquare (a:K) := by
  rintro ⟨z,hz⟩
  have he := congrArg f hz
  simp only [map_mul,map_ratCast] at he
  have hc := congrArg HahnSeries.leadingCoeff he
  have hconst : HahnSeries.leadingCoeff (a : LaurentSeries ℚ)=a := by
    rw [←HahnSeries.single_zero_ratCast]
    simpa only [Rat.cast_id] using (HahnSeries.leadingCoeff_of_single (a:= (0:ℤ)) (r:=a))
  rw [hconst,HahnSeries.leadingCoeff_mul] at hc
  exact ha ⟨(f z).leadingCoeff,hc⟩

end Z2Z4Rank6
