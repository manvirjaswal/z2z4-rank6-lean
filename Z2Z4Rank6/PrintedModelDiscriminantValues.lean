module

public import Z2Z4Rank6.PrintedModelReduction

@[expose] public section

/-!
# Exact normalized discriminant values at every prime

These are valuations of the globally minimal printed EC, JG and J2
equations (Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1 and
Propositions 7.2/8.1). A closed integer factorization and a prime-to-p
residual factor compute each value. The convention is multiplicative:
an additive valuation n is represented by exp(-n).
-/
namespace Z2Z4Rank6.PrintedModelReduction

open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open PrintedModelMinimality MinimalitySmallDiscriminant

noncomputable section

def discriminantExponent (i : Fin 3) (p : ℕ) : ℕ :=
  match i.val with
  | 0 => if p=2 then 8 else if p=3 then 12 else if p=5 then 2 else
      if p=7 then 4 else if p=11 then 4 else 0
  | 1 => if p=2 then 10 else if p=3 then 8 else if p=5 then 4 else
      if p=7 then 8 else if p=11 then 4 else if p=37 then 2 else 0
  | _ => if p=2 then 12 else if p=3 then 8 else if p=5 then 4 else
      if p=7 then 8 else if p=11 then 8 else if p=17 then 4 else
      if p=19 then 8 else if p=23 then 8 else if p=29 then 2 else
      if p=197 then 2 else if p=233 then 2 else 0

def discriminantResidual (i : Fin 3) (p : ℕ) : ℤ :=
  discriminantProduct i / (p:ℤ)^(discriminantExponent i p)

/-- The exact exponent and the residual integer are checked at
every prime in each discriminant's support. -/
theorem discriminant_residual_certificate (i : Fin 3) (p : ℕ)
    (hp : p ∈ badPrimes i) :
    discriminantProduct i=(p:ℤ)^(discriminantExponent i p)*discriminantResidual i p ∧
      ¬(p:ℤ)∣discriminantResidual i p := by
  fin_cases i
  · have hp' : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 := by simpa [badPrimes] using hp
    rcases hp' with rfl|rfl|rfl|rfl|rfl <;>
      norm_num [discriminantProduct,discriminantResidual,discriminantExponent]
  · have hp' : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=37 := by simpa [badPrimes] using hp
    rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [discriminantProduct,discriminantResidual,discriminantExponent]
  · have hp' : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=17 ∨ p=19 ∨ p=23 ∨
        p=29 ∨ p=197 ∨ p=233 := by simpa [badPrimes] using hp
    rcases hp' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [discriminantProduct,discriminantResidual,discriminantExponent]

theorem discriminantExponent_eq_zero_of_not_mem (i : Fin 3) (p : ℕ)
    (hp : p ∉ badPrimes i) : discriminantExponent i p=0 := by
  fin_cases i
  · have h : p≠2 ∧ p≠3 ∧ p≠5 ∧ p≠7 ∧ p≠11 := by simpa [badPrimes] using hp
    rcases h with ⟨h2,h3,h5,h7,h11⟩
    simp [discriminantExponent,h2,h3,h5,h7,h11]
  · have h : p≠2 ∧ p≠3 ∧ p≠5 ∧ p≠7 ∧ p≠11 ∧ p≠37 := by simpa [badPrimes] using hp
    rcases h with ⟨h2,h3,h5,h7,h11,h37⟩
    simp [discriminantExponent,h2,h3,h5,h7,h11,h37]
  · have h : p≠2 ∧ p≠3 ∧ p≠5 ∧ p≠7 ∧ p≠11 ∧ p≠17 ∧ p≠19 ∧ p≠23 ∧
        p≠29 ∧ p≠197 ∧ p≠233 := by simpa [badPrimes] using hp
    rcases h with ⟨h2,h3,h5,h7,h11,h17,h19,h23,h29,h197,h233⟩
    simp [discriminantExponent,h2,h3,h5,h7,h11,h17,h19,h23,h29,h197,h233]

theorem discriminantExponent_pos_iff (i : Fin 3) (p : ℕ) :
    0<discriminantExponent i p ↔ p ∈ badPrimes i := by
  by_cases hp : p ∈ badPrimes i
  · have hpos : 0<discriminantExponent i p := by
      fin_cases i
      · have h : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 := by simpa [badPrimes] using hp
        rcases h with rfl|rfl|rfl|rfl|rfl <;> norm_num [discriminantExponent]
      · have h : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=37 := by simpa [badPrimes] using hp
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [discriminantExponent]
      · have h : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=17 ∨ p=19 ∨ p=23 ∨
            p=29 ∨ p=197 ∨ p=233 := by simpa [badPrimes] using hp
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
          norm_num [discriminantExponent]
    exact iff_of_true hpos hp
  · rw [discriminantExponent_eq_zero_of_not_mem i p hp]
    simp [hp]

/-- Exact normalized DVR discriminant valuation for every rational prime
of each printed equation. -/
theorem discriminant_value (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    valuation (Padic p) (maximalIdeal (PadicInt p))
      ((rationalModel i).map (Rat.castHom (Padic p))).Δ=
      exp (-(discriminantExponent i p : ℤ)) := by
  by_cases hp : p ∈ badPrimes i
  · obtain ⟨hfactor,hunit⟩ := discriminant_residual_certificate i p hp
    have hv := padic_integer_value p (discriminantExponent i p) (discriminantResidual i p) hunit
    have hcast := congrArg (Int.castRingHom (Padic p))
      ((discriminant_factorization i).trans hfactor)
    simp only [map_mul,map_pow,map_natCast,Int.coe_castRingHom] at hcast
    rw [←hcast] at hv
    rw [←localModel_eq]
    simpa only [localModel,WeierstrassCurve.baseChange,WeierstrassCurve.map_Δ,
      Int.coe_castRingHom,map_intCast] using hv
  · have hgood := good_of_not_mem i p hp
    rw [discriminantExponent_eq_zero_of_not_mem i p hp]
    simpa only [Nat.cast_zero,neg_zero,exp_zero,localModel_eq] using hgood.goodReduction

theorem ec_discriminant_value (p : ℕ) [Fact p.Prime] :
    valuation (Padic p) (maximalIdeal (PadicInt p))
      (EC.map (Rat.castHom (Padic p))).Δ=exp (-(discriminantExponent 0 p : ℤ)) := by
  exact discriminant_value 0 p

theorem jg_discriminant_value (p : ℕ) [Fact p.Prime] :
    valuation (Padic p) (maximalIdeal (PadicInt p))
      (JG.map (Rat.castHom (Padic p))).Δ=exp (-(discriminantExponent 1 p : ℤ)) := by
  exact discriminant_value 1 p

theorem j2_discriminant_value (p : ℕ) [Fact p.Prime] :
    valuation (Padic p) (maximalIdeal (PadicInt p))
      (J2.map (Rat.castHom (Padic p))).Δ=exp (-(discriminantExponent 2 p : ℤ)) := by
  exact discriminant_value 2 p

end
end Z2Z4Rank6.PrintedModelReduction
