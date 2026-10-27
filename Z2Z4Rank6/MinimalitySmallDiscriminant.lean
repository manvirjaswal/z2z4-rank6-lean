module

public import Z2Z4Rank6.Minimality
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

/-!
# Minimality when the discriminant valuation is less than twelve

An integral equation whose additive discriminant valuation is below twelve
is minimal: an integral change lowering it would have to lower it by a
positive multiple of twelve. The proof uses the normalized DVR
valuation and Mathlib's IsMinimal predicate. This supplies arithmetic checks for the printed models
in Jaswal, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.MinimalitySmallDiscriminant

open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
noncomputable section

private theorem factor_le_one {a b : ℤᵐ⁰}
    (hb : exp (-12 : ℤ)<b) (hab : a^12*b≤1) : a≤1 := by
  induction a using WithZero.expRecOn with
  | zero => simp
  | exp n =>
    by_contra hn
    have hn0 : 0<n := by simpa only [exp_le_one_iff,not_le] using hn
    have hprod : 1≤exp n^12*exp (-12 : ℤ) := by
      rw [←exp_nsmul,←exp_add,one_le_exp_iff]
      simp only [nsmul_eq_mul]
      omega
    have hlt : exp n^12*exp (-12 : ℤ)<exp n^12*b :=
      mul_lt_mul_of_pos_left hb (pow_pos exp_pos _)
    exact (not_lt_of_ge hab) (hprod.trans_lt hlt)

/-- A strict normalized multiplicative bound exp(-12)<v(Δ) gives the
minimality of an integral Weierstrass equation over any DVR. -/
theorem isMinimal_of_discriminant_gt
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [IsIntegral R W]
    (hdisc : exp (-12 : ℤ)<valuation K (maximalIdeal R) W.Δ) : IsMinimal R W := by
  refine ⟨⟨by simpa only [one_smul] using (inferInstance : IsIntegral R W),?_⟩⟩
  intro C hC _
  let : IsIntegral R (C • W) := hC
  have hv : valuation K (maximalIdeal R) (C • W).Δ≤1 := by
    obtain ⟨r,hr⟩ := Δ_integral_of_isIntegral R (C • W)
    rw [←hr]
    exact valuation_le_one (maximalIdeal R) r
  rw [variableChange_Δ,map_mul,map_pow] at hv
  have hu := factor_le_one hdisc hv
  change (valuation_Δ_aux R (C • W) : ℤᵐ⁰)≤(valuation_Δ_aux R (1 • W) : ℤᵐ⁰)
  rw [one_smul,valuation_Δ_aux_eq_of_isIntegral,valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ,map_mul,map_pow]
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

/-- The normalized height-one DVR valuation sends the p-adic
uniformizer p to exp(-1), without comparing real-valued norms. -/
theorem padic_uniformizer_value (p : ℕ) [Fact p.Prime] :
    valuation (Padic p) (maximalIdeal (PadicInt p)) (p : Padic p)=exp (-1 : ℤ) := by
  have h := (maximalIdeal (PadicInt p)).intValuation_singleton
    (PadicInt.irreducible_p.ne_zero) (PadicInt.maximalIdeal_eq_span_p (p:=p))
  simpa only [←valuation_of_algebraMap (K:=Padic p),map_natCast] using h

/-- A unit has normalized DVR valuation one. -/
theorem valuation_unit
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (a : R) (ha : IsUnit a) :
    valuation K (maximalIdeal R) (algebraMap R K a)=1 := by
  obtain ⟨u,rfl⟩ := ha
  apply le_antisymm (valuation_le_one (maximalIdeal R) _)
  calc
    1=valuation K (maximalIdeal R) (algebraMap R K (u:R))*
      valuation K (maximalIdeal R) (algebraMap R K ((u⁻¹:Rˣ):R)) := by
      rw [←map_mul,←map_mul,Units.mul_inv,map_one,map_one]
    _≤valuation K (maximalIdeal R) (algebraMap R K (u:R))*1 :=
      mul_le_mul_of_nonneg_left (valuation_le_one (maximalIdeal R) _) zero_le
    _=_ := mul_one _

/-- Any integer prime to p is a unit in the p-adic integer ring. -/
theorem padicInt_isUnit_intCast (p : ℕ) [Fact p.Prime] (n : ℤ)
    (hn : ¬(p:ℤ)∣n) : IsUnit (n : PadicInt p) := by
  by_contra hu
  exact hn (PadicInt.norm_intCast_lt_one_iff.mp (PadicInt.not_isUnit_iff.mp hu))

/-- A closed integer factorization Δ=p^n*d with p∤d computes the
normalized DVR discriminant valuation. -/
theorem padic_integer_value (p : ℕ) [Fact p.Prime] (n : ℕ) (d : ℤ)
    (hd : ¬(p:ℤ)∣d) :
    valuation (Padic p) (maximalIdeal (PadicInt p))
      ((p : Padic p)^n*(d : Padic p))=exp (-(n:ℤ)) := by
  have hu := valuation_unit (K:=Padic p) (PadicInt p) (d : PadicInt p)
    (padicInt_isUnit_intCast p d hd)
  simp only [map_intCast] at hu
  rw [map_mul,map_pow,padic_uniformizer_value,hu,mul_one,←exp_nsmul]
  congr 1
  simp

end
end Z2Z4Rank6.MinimalitySmallDiscriminant
