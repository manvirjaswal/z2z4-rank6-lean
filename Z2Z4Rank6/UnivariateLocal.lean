module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.LaurentSeries

@[expose] public section

/-!
# A shifted local embedding of Q(t)

The substitution t=r+T embeds the rational-function field into Q((T)).
This is the formal local chart used for smooth-fiber specialization in
Proposition 2.3 of M. Jaswal, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.UnivariateLocal

open Polynomial
noncomputable section

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

/-- The local parameter t=r+T at an arbitrary rational parameter. -/
def mSeries (r : ℚ) : PS := PowerSeries.C r+PowerSeries.X

@[simp] theorem mSeries_constant (r : ℚ) : PowerSeries.constantCoeff (mSeries r)=r := by
  simp [mSeries]

@[simp] theorem mSeries_coeff_one (r : ℚ) : PowerSeries.coeff 1 (mSeries r)=1 := by
  simp [mSeries]

/-- Shift a polynomial and include it in the power-series ring. -/
def polynomialSeries (r : ℚ) : ℚ[X] →+* PS :=
  Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.algEquivAevalXAddC r).toRingHom

theorem polynomialSeries_injective (r : ℚ) : Function.Injective (polynomialSeries r) :=
  (Polynomial.coe_injective ℚ).comp (Polynomial.algEquivAevalXAddC r).injective

@[simp] theorem polynomialSeries_X (r : ℚ) : polynomialSeries r Polynomial.X=mSeries r := by
  simp [polynomialSeries, Polynomial.algEquivAevalXAddC_apply, mSeries, add_comm]

@[simp] theorem polynomialSeries_C (r c : ℚ) :
    polynomialSeries r (Polynomial.C c)=PowerSeries.C c := by
  simp [polynomialSeries, Polynomial.algEquivAevalXAddC_apply]

/-- Every coefficient is the corresponding coefficient of the shifted polynomial. -/
theorem polynomialSeries_coeff (r : ℚ) (p : ℚ[X]) (n : ℕ) :
    PowerSeries.coeff n (polynomialSeries r p)=(p.comp (Polynomial.X+Polynomial.C r)).coeff n := by
  simp [polynomialSeries, Polynomial.algEquivAevalXAddC_apply, ← Polynomial.comp_eq_aeval]

@[simp] theorem polynomialSeries_constant (r : ℚ) (p : ℚ[X]) :
    PowerSeries.constantCoeff (polynomialSeries r p)=p.eval r := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, polynomialSeries_coeff]
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp

/-- The shifted polynomial embedding into the Laurent-series field. -/
def polynomialLaurent (r : ℚ) : ℚ[X] →+* LS :=
  (algebraMap PS LS).comp (polynomialSeries r)

theorem polynomialLaurent_injective (r : ℚ) : Function.Injective (polynomialLaurent r) :=
  (IsFractionRing.injective PS LS).comp (polynomialSeries_injective r)

/-- The unique field embedding extending shifted polynomial substitution. -/
def baseEmbedding (r : ℚ) : RatFunc ℚ →+* LS :=
  IsFractionRing.lift (K := RatFunc ℚ) (polynomialLaurent_injective r)

@[simp] theorem baseEmbedding_polynomial (r : ℚ) (p : ℚ[X]) :
    baseEmbedding r (algebraMap ℚ[X] (RatFunc ℚ) p)=polynomialLaurent r p :=
  IsFractionRing.lift_algebraMap (polynomialLaurent_injective r) p

@[simp] theorem baseEmbedding_X (r : ℚ) :
    baseEmbedding r RatFunc.X=algebraMap PS LS (mSeries r) := by
  rw [← RatFunc.algebraMap_X, baseEmbedding_polynomial]
  simp [polynomialLaurent]

@[simp] theorem baseEmbedding_C (r c : ℚ) :
    baseEmbedding r (RatFunc.C c)=algebraMap PS LS (PowerSeries.C c) := by
  rw [← RatFunc.algebraMap_C, baseEmbedding_polynomial]
  simp [polynomialLaurent]

theorem baseEmbedding_injective (r : ℚ) : Function.Injective (baseEmbedding r) :=
  (baseEmbedding r).injective

/-- The integral power-series representative of a rational function regular
at r, constructed from its reduced numerator and denominator. -/
def regularSeries (r : ℚ) (f : RatFunc ℚ) : PS :=
  polynomialSeries r (RatFunc.num f)*(polynomialSeries r (RatFunc.denom f))⁻¹

@[simp] theorem regularSeries_constant (r : ℚ) (f : RatFunc ℚ) :
    PowerSeries.constantCoeff (regularSeries r f)=RatFunc.eval (RingHom.id ℚ) r f := by
  simp [regularSeries, PowerSeries.constantCoeff_inv, RatFunc.eval, div_eq_mul_inv]

/-- A rational function with nonvanishing reduced denominator has an
integral representative in the formal chart. -/
theorem baseEmbedding_regular (r : ℚ) (f : RatFunc ℚ)
    (hden : (RatFunc.denom f).eval r ≠ 0) :
    baseEmbedding r f=algebraMap PS LS (regularSeries r f) := by
  have hc : PowerSeries.constantCoeff (polynomialSeries r (RatFunc.denom f)) ≠ 0 := by
    simpa using hden
  have hn : polynomialLaurent r (RatFunc.denom f) ≠ 0 := by
    simpa only [map_zero] using (polynomialLaurent_injective r).ne (RatFunc.denom_ne_zero f)
  have hmul : algebraMap PS LS (regularSeries r f)*polynomialLaurent r (RatFunc.denom f)=
      polynomialLaurent r (RatFunc.num f) := by
    change algebraMap PS LS (regularSeries r f)*
      algebraMap PS LS (polynomialSeries r (RatFunc.denom f))=
      algebraMap PS LS (polynomialSeries r (RatFunc.num f))
    rw [← map_mul]
    congr 1
    calc
      regularSeries r f*polynomialSeries r (RatFunc.denom f) =
          polynomialSeries r (RatFunc.num f)*
            (polynomialSeries r (RatFunc.denom f)*(polynomialSeries r (RatFunc.denom f))⁻¹) := by
        dsimp [regularSeries]
        ring
      _ = polynomialSeries r (RatFunc.num f) := by
        rw [PowerSeries.mul_inv_cancel _ hc,mul_one]
  have he := congrArg (baseEmbedding r) (RatFunc.num_div_denom f)
  rw [map_div₀,baseEmbedding_polynomial,baseEmbedding_polynomial] at he
  exact he.symm.trans ((div_eq_iff hn).mpr hmul.symm)


/-- Mapping the inverse of a power series with nonzero constant coefficient
agrees with inversion in the Laurent-series field. -/
theorem map_series_inv (d : PS) (hd : PowerSeries.constantCoeff d ≠ 0) :
    algebraMap PS LS d⁻¹=(algebraMap PS LS d)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [←map_mul,mul_comm d⁻¹ d,PowerSeries.mul_inv_cancel d hd,map_one]


end
end Z2Z4Rank6.UnivariateLocal
