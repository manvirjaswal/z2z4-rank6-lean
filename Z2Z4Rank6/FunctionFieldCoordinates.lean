module

public import Z2Z4Rank6.FunctionFieldLocal
public import Z2Z4Rank6.CongruenceBase

@[expose] public section

/-!
# Integral local coordinates of the six sections

The common denominator in Proposition 6.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117, is a unit in Q[[T]] at the printed point c0.
This file constructs power-series coordinates for all six embedded
generic points and verifies their constant terms.
-/

namespace Z2Z4Rank6.FunctionFieldLocal

open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

/-- The family commutes with coefficient ring homomorphisms. -/
theorem map_family {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (t : R) : (X t).map f = X (f t) := by
  ext <;> simp [X, E, a, b, map_ofNat]

/-- The common denominator is nonzero at the printed rational point. -/
theorem base_denominator_ne_zero : sectionDenominator baseC0.m ≠ 0 := by
  norm_num [sectionDenominator, baseC0]

/-- The common denominator has nonzero constant coefficient in Q[[T]]. -/
theorem series_denominator_constant_ne_zero :
    PowerSeries.constantCoeff (sectionDenominator mSeries) ≠ 0 := by
  rw [map_sectionDenominator, mSeries_constant]
  exact base_denominator_ne_zero

/-- The denominator is a unit, not merely a nonzero power series. -/
theorem series_denominator_isUnit : IsUnit (sectionDenominator mSeries) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  exact series_denominator_constant_ne_zero

/-- Integral abscissa of the j-th generic section in the formal local chart. -/
def xSeries (j : Fin 6) : PS :=
  sectionXNumerator mSeries j*(sectionDenominator mSeries)⁻¹

/-- Integral ordinate of the j-th generic section in the formal local chart. -/
def ySeries (j : Fin 6) : PS :=
  sectionYNumerator mSeries uSeries vSeries j*(sectionDenominator mSeries)⁻¹

/-- The local abscissa has precisely its printed specialization as constant term. -/
theorem xSeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (xSeries j) = sixX baseC0.m j := by
  rw [xSeries, map_mul, map_sectionXNumerator, PowerSeries.constantCoeff_inv,
    map_sectionDenominator, mSeries_constant]
  rw [← denominator_mul_sixX baseC0.m (by norm_num [baseC0])
    (by norm_num [baseC0]) j]
  field_simp [base_denominator_ne_zero]

/-- The local ordinate has precisely its printed signed specialization as
constant term, with the positive roots u0 and v0. -/
theorem ySeries_constant (j : Fin 6) :
    PowerSeries.constantCoeff (ySeries j) = sixY baseC0.m baseC0.u baseC0.v j := by
  rw [ySeries, map_mul, map_sectionYNumerator, PowerSeries.constantCoeff_inv,
    map_sectionDenominator, mSeries_constant, uSeries_spec.2, vSeries_spec.2]
  rw [← denominator_mul_sixY baseC0.m baseC0.u baseC0.v baseC0.u_sq baseC0.v_sq
    (by norm_num [baseC0]) baseC0.u_ne_zero baseC0.v_ne_zero
    (by norm_num [baseC0]) (by norm_num [baseC0]) j]
  field_simp [base_denominator_ne_zero]

private theorem first_factor_ne_zero : 3*FunctionField.m^2+242 ≠ 0 := by
  intro h
  have heq := FunctionField.u_sq
  rw [h, mul_zero] at heq
  exact (pow_ne_zero 2 FunctionField.u_ne_zero) heq

private theorem second_factor_ne_zero : 2*FunctionField.m^2+243 ≠ 0 := by
  intro h
  have heq := FunctionField.v_sq
  rw [h, mul_zero] at heq
  exact (pow_ne_zero 2 FunctionField.v_ne_zero) heq

private theorem denominator_laurent_ne_zero :
    algebraMap PS LS (sectionDenominator mSeries) ≠ 0 := by
  have hPS : sectionDenominator mSeries ≠ 0 := by
    intro h
    apply series_denominator_constant_ne_zero
    rw [h, map_zero]
  simpa only [map_zero] using (IsFractionRing.injective PS LS).ne hPS

private theorem denominator_mul_xSeries (j : Fin 6) :
    sectionDenominator mSeries*xSeries j=sectionXNumerator mSeries j := by
  rw [xSeries, mul_left_comm,
    PowerSeries.mul_inv_cancel _ series_denominator_constant_ne_zero, mul_one]

private theorem denominator_mul_ySeries (j : Fin 6) :
    sectionDenominator mSeries*ySeries j=sectionYNumerator mSeries uSeries vSeries j := by
  rw [ySeries, mul_left_comm,
    PowerSeries.mul_inv_cancel _ series_denominator_constant_ne_zero, mul_one]

/-- The embedded generic abscissa is exactly the image of its integral
power-series coordinate. -/
theorem embedding_sixX (j : Fin 6) :
    embedding (sixX FunctionField.m j) = algebraMap PS LS (xSeries j) := by
  apply mul_left_cancel₀ denominator_laurent_ne_zero
  have h := congrArg embedding
    (denominator_mul_sixX FunctionField.m FunctionField.m_ne_zero first_factor_ne_zero j)
  have heq : algebraMap PS LS (sectionDenominator mSeries)*
      embedding (sixX FunctionField.m j)=algebraMap PS LS (sectionXNumerator mSeries j) := by
    simpa only [map_mul, map_sectionDenominator, map_sectionXNumerator, embedding_m] using h
  rw [heq, ← map_mul, denominator_mul_xSeries]

/-- The embedded generic ordinate is exactly the image of its integral
power-series coordinate, including the printed choice of signs. -/
theorem embedding_sixY (j : Fin 6) :
    embedding (sixY FunctionField.m FunctionField.u FunctionField.v j) =
      algebraMap PS LS (ySeries j) := by
  apply mul_left_cancel₀ denominator_laurent_ne_zero
  have h := congrArg embedding
    (denominator_mul_sixY FunctionField.m FunctionField.u FunctionField.v
      FunctionField.u_sq FunctionField.v_sq FunctionField.m_ne_zero FunctionField.u_ne_zero
      FunctionField.v_ne_zero first_factor_ne_zero second_factor_ne_zero j)
  have heq : algebraMap PS LS (sectionDenominator mSeries)*
      embedding (sixY FunctionField.m FunctionField.u FunctionField.v j)=
      algebraMap PS LS (sectionYNumerator mSeries uSeries vSeries j) := by
    simpa only [map_mul, map_sectionDenominator, map_sectionYNumerator,
      embedding_m, embedding_u, embedding_v] using h
  rw [heq, ← map_mul, denominator_mul_ySeries]

/-- The integral family over Q[[T]] at c0. -/
def seriesCurve : WeierstrassCurve PS := X mSeries

/-- Its constant reduction is exactly the original rational fiber at c0. -/
theorem seriesCurve_constant : seriesCurve.map PowerSeries.constantCoeff = X baseC0.m := by
  rw [seriesCurve, map_family, mSeries_constant]

/-- Its Laurent generic fiber is exactly the mapped curve over Q(C). -/
theorem seriesCurve_laurent :
    seriesCurve.map (algebraMap PS LS) = (X FunctionField.m).map embedding := by
  rw [seriesCurve, map_family, map_family, embedding_m]

instance constantFiberElliptic : (seriesCurve.map PowerSeries.constantCoeff).IsElliptic := by
  rw [seriesCurve_constant]
  exact X_good_of_congruent 0 (baseC0_integral 0).1 rfl

instance laurentFiberElliptic : (seriesCurve.map (algebraMap PS LS)).IsElliptic := by
  rw [seriesCurve_laurent]
  infer_instance

end
end Z2Z4Rank6.FunctionFieldLocal
