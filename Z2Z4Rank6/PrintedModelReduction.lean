module

public import Z2Z4Rank6.PrintedModelMinimality

@[expose] public section

/-!
# Reduction types of the three printed integral equations

The equations are EC, JG and J2 in Jaswal, DOI 10.5281/zenodo.23437117,
Lemma 4.1 and Propositions 7.2/8.1. Exact integer factorizations, the
proved minimality of these equations, and the normalized DVR
valuation give Mathlib's good, multiplicative and additive reduction
predicates at every rational prime.
-/
namespace Z2Z4Rank6.PrintedModelReduction

open WeierstrassCurve WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum
open PrintedModelMinimality MinimalitySmallDiscriminant

noncomputable section

def badPrimes : Fin 3 → Finset ℕ :=
  ![{2,3,5,7,11}, {2,3,5,7,11,37}, {2,3,5,7,11,17,19,23,29,197,233}]

def discriminantProduct : Fin 3 → ℤ :=
  ![2^8*3^12*5^2*7^4*11^4,
    2^10*3^8*5^4*7^8*11^4*37^2,
    2^12*3^8*5^4*7^8*11^8*17^4*19^8*23^8*29^2*197^2*233^2]

def oddC4 : Fin 3 → ℤ := ![412861,78292201,23782438727492469342481]

theorem discriminant_factorization (i : Fin 3) :
    (integerModel i).Δ = discriminantProduct i := by
  rw [discriminant_two_factorization]
  fin_cases i <;> norm_num [twoExponent,oddDiscriminant,discriminantProduct]

theorem c4_two_factorization (i : Fin 3) :
    (integerModel i).c₄ = 2^4*oddC4 i := by
  fin_cases i <;> norm_num [integerModel,oddC4,WeierstrassCurve.c₄,
    WeierstrassCurve.b₂,WeierstrassCurve.b₄]

theorem oddC4_odd (i : Fin 3) : ¬(2:ℤ) ∣ oddC4 i := by
  fin_cases i <;> norm_num [oddC4]

theorem two_mem_badPrimes (i : Fin 3) : 2 ∈ badPrimes i := by
  fin_cases i <;> decide

private theorem prime_dvd_prime_int_iff {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p:ℤ) ∣ (q:ℤ) ↔ p=q := by
  exact_mod_cast Nat.prime_dvd_prime_iff_eq hp hq

/-- The full list of bad-prime candidates is proved from the
integer discriminant, without a conductor table. -/
theorem prime_dvd_discriminant_iff (i : Fin 3) (p : ℕ) [hp : Fact p.Prime] :
    (p:ℤ) ∣ (integerModel i).Δ ↔ p ∈ badPrimes i := by
  have hP : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h2 : (p:ℤ)∣2 ↔ p=2 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 2)
  have h3 : (p:ℤ)∣3 ↔ p=3 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 3)
  have h5 : (p:ℤ)∣5 ↔ p=5 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 5)
  have h7 : (p:ℤ)∣7 ↔ p=7 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 7)
  have h11 : (p:ℤ)∣11 ↔ p=11 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 11)
  rw [discriminant_factorization]
  fin_cases i
  · change (p:ℤ)∣2^8*3^12*5^2*7^4*11^4 ↔ p ∈ badPrimes 0
    simp (disch := norm_num) only [hP.dvd_mul,hP.dvd_pow_iff_dvd]
    simp [badPrimes,h2,h3,h5,h7,h11,or_assoc]
  · change (p:ℤ)∣2^10*3^8*5^4*7^8*11^4*37^2 ↔ p ∈ badPrimes 1
    simp (disch := norm_num) only [hP.dvd_mul,hP.dvd_pow_iff_dvd]
    have h37 : (p:ℤ)∣37 ↔ p=37 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 37)
    simp [badPrimes,h2,h3,h5,h7,h11,h37,or_assoc]
  · change (p:ℤ)∣2^12*3^8*5^4*7^8*11^8*17^4*19^8*23^8*29^2*197^2*233^2 ↔
      p ∈ badPrimes 2
    simp (disch := norm_num) only [hP.dvd_mul,hP.dvd_pow_iff_dvd]
    have h17 : (p:ℤ)∣17 ↔ p=17 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 17)
    have h19 : (p:ℤ)∣19 ↔ p=19 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 19)
    have h23 : (p:ℤ)∣23 ↔ p=23 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 23)
    have h29 : (p:ℤ)∣29 ↔ p=29 := prime_dvd_prime_int_iff hp.out (by decide : Nat.Prime 29)
    have h197 : (p:ℤ)∣197 ↔ p=197 := prime_dvd_prime_int_iff hp.out (by norm_num : Nat.Prime 197)
    have h233 : (p:ℤ)∣233 ↔ p=233 := prime_dvd_prime_int_iff hp.out (by norm_num : Nat.Prime 233)
    simp [badPrimes,h2,h3,h5,h7,h11,h17,h19,h23,h29,h197,h233,or_assoc]

/-- A prime-to-p integer has normalized multiplicative valuation one. -/
theorem integer_value_eq_one (p : ℕ) [Fact p.Prime] (n : ℤ)
    (hn : ¬(p:ℤ)∣n) :
    valuation (Padic p) (maximalIdeal (PadicInt p)) (n : Padic p)=1 := by
  simpa only [map_intCast] using valuation_unit (K:=Padic p) (PadicInt p)
    (n : PadicInt p) (padicInt_isUnit_intCast p n hn)

/-- An integer divisible by p has normalized multiplicative valuation
strictly below one; this also includes the integer zero. -/
theorem integer_value_lt_one (p : ℕ) [Fact p.Prime] (n : ℤ)
    (hn : (p:ℤ)∣n) :
    valuation (Padic p) (maximalIdeal (PadicInt p)) (n : Padic p)<1 := by
  obtain ⟨m,rfl⟩ := hn
  have hm := valuation_le_one (K:=Padic p) (maximalIdeal (PadicInt p)) (m : PadicInt p)
  simp only [map_intCast] at hm
  simp only [Int.cast_mul,Int.cast_natCast,map_mul,padic_uniformizer_value]
  calc
    _ ≤ exp (-1 : ℤ)*1 := mul_le_mul_of_nonneg_left hm zero_le
    _ < 1 := by simpa only [mul_one,exp_lt_one_iff] using (by decide : (-1:ℤ)<0)

private theorem localModel_discriminant (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    (localModel i p).Δ = ((integerModel i).Δ : Padic p) := by
  simp only [localModel,WeierstrassCurve.baseChange,WeierstrassCurve.map_Δ,
    Int.coe_castRingHom,map_intCast]

private theorem localModel_c4 (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    (localModel i p).c₄ = ((integerModel i).c₄ : Padic p) := by
  simp only [localModel,WeierstrassCurve.baseChange,WeierstrassCurve.map_c₄,
    Int.coe_castRingHom,map_intCast]

theorem model_minimal (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    IsMinimal (PadicInt p) (localModel i p) := by
  rw [localModel_eq]
  fin_cases i
  · exact ec_minimal p
  · exact jg_minimal p
  · exact j2_minimal p

/-- At an odd discriminant prime, c₄ is a unit, by the exact integer
Bezout certificate c₄ r + Δ s = 16. -/
theorem c4_not_dvd_at_odd_bad (i : Fin 3) (p : ℕ) [hp : Fact p.Prime]
    (hbad : p ∈ badPrimes i) (hodd : p≠2) : ¬(p:ℤ) ∣ (integerModel i).c₄ := by
  intro hc
  have hd := (prime_dvd_discriminant_iff i p).mpr hbad
  have h16 : (p:ℤ)∣16 := by
    rw [←invariant_bezout i]
    exact dvd_add (dvd_mul_of_dvd_right hc _) (dvd_mul_of_dvd_right hd _)
  have h16N : p∣2^4 := by norm_num at h16 ⊢; exact_mod_cast h16
  have h2 := hp.out.dvd_of_dvd_pow h16N
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out (by decide)).mp h2)

theorem good_of_not_mem (i : Fin 3) (p : ℕ) [Fact p.Prime]
    (hp : p ∉ badPrimes i) : HasGoodReduction (PadicInt p) (localModel i p) := by
  let := model_minimal i p
  refine {goodReduction := ?_}
  rw [localModel_discriminant]
  exact integer_value_eq_one p _ (fun h => hp ((prime_dvd_discriminant_iff i p).mp h))

theorem multiplicative_of_mem_of_ne_two (i : Fin 3) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ badPrimes i) (hodd : p≠2) :
    HasMultiplicativeReduction (PadicInt p) (localModel i p) := by
  let := model_minimal i p
  refine {badReduction := ?_,multiplicativeReduction := ?_}
  · rw [localModel_discriminant]
    exact integer_value_lt_one p _ ((prime_dvd_discriminant_iff i p).mpr hp)
  · rw [localModel_c4]
    exact integer_value_eq_one p _ (c4_not_dvd_at_odd_bad i p hp hodd)

local instance printedReductionPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem c4_value_two (i : Fin 3) :
    valuation (Padic 2) (maximalIdeal (PadicInt 2)) (localModel i 2).c₄=exp (-4 : ℤ) := by
  rw [localModel_c4]
  have hv := padic_integer_value 2 4 (oddC4 i) (oddC4_odd i)
  have hcast := congrArg (Int.castRingHom (Padic 2)) (c4_two_factorization i)
  simp only [map_mul,map_pow,map_ofNat,Int.coe_castRingHom] at hcast
  rw [hcast]
  exact hv

theorem additive_at_two (i : Fin 3) :
    HasAdditiveReduction (PadicInt 2) (localModel i 2) := by
  let := model_minimal i 2
  refine {badReduction := ?_,additiveReduction := ?_}
  · rw [discriminant_value_two,exp_lt_one_iff]
    fin_cases i <;> norm_num [twoExponent]
  · rw [c4_value_two,exp_lt_one_iff]
    decide

/-- Exactly the listed discriminant primes fail good reduction. -/
theorem hasGoodReduction_iff (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    HasGoodReduction (PadicInt p) (localModel i p) ↔ p ∉ badPrimes i := by
  refine ⟨?_,good_of_not_mem i p⟩
  intro hgood hbad
  by_cases hp : p=2
  · subst p
    exact HasAdditiveReduction.not_hasGoodReduction (PadicInt 2) (additive_at_two i) hgood
  · exact HasMultiplicativeReduction.not_hasGoodReduction (PadicInt p)
      (multiplicative_of_mem_of_ne_two i p hbad hp) hgood

/-- The odd members of the bad-prime list are precisely the primes of
multiplicative reduction. -/
theorem hasMultiplicativeReduction_iff (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    HasMultiplicativeReduction (PadicInt p) (localModel i p) ↔ p ∈ badPrimes i ∧ p≠2 := by
  refine ⟨?_,fun h => multiplicative_of_mem_of_ne_two i p h.1 h.2⟩
  intro h
  constructor
  · by_contra hn
    exact HasMultiplicativeReduction.not_hasGoodReduction (PadicInt p) h
      (good_of_not_mem i p hn)
  · intro hp
    subst p
    exact HasAdditiveReduction.not_hasMultiplicativeReduction (PadicInt 2) (additive_at_two i) h

/-- All three printed equations have additive reduction precisely at two. -/
theorem hasAdditiveReduction_iff (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    HasAdditiveReduction (PadicInt p) (localModel i p) ↔ p=2 := by
  refine ⟨?_,fun hp => hp ▸ additive_at_two i⟩
  intro h
  by_contra hp
  by_cases hbad : p ∈ badPrimes i
  · exact HasMultiplicativeReduction.not_hasAdditiveReduction (PadicInt p)
      (multiplicative_of_mem_of_ne_two i p hbad hp) h
  · exact HasGoodReduction.not_hasAdditiveReduction (PadicInt p) (good_of_not_mem i p hbad) h

/-- The three classifications for the rational equation after its
canonical embedding into the p-adic field. -/
theorem model_reduction_types (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    (HasGoodReduction (PadicInt p) ((rationalModel i).map (Rat.castHom (Padic p))) ↔
      p ∉ badPrimes i) ∧
    (HasMultiplicativeReduction (PadicInt p) ((rationalModel i).map (Rat.castHom (Padic p))) ↔
      p ∈ badPrimes i ∧ p≠2) ∧
    (HasAdditiveReduction (PadicInt p) ((rationalModel i).map (Rat.castHom (Padic p))) ↔
      p=2) := by
  have h := And.intro (hasGoodReduction_iff i p)
    (And.intro (hasMultiplicativeReduction_iff i p) (hasAdditiveReduction_iff i p))
  simpa only [localModel_eq] using h

theorem not_good_iff_bad (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    ¬HasGoodReduction (PadicInt p) ((rationalModel i).map (Rat.castHom (Padic p))) ↔
      p ∈ badPrimes i := by
  simpa only [not_not] using not_congr (model_reduction_types i p).1

/-- The normalized valuations at two are exactly v(c₄)=4 and
v(Δ)=8,10,12, respectively; exp(-n) is the DVR multiplicative convention. -/
theorem two_adic_invariant_values (i : Fin 3) :
    valuation (Padic 2) (maximalIdeal (PadicInt 2))
      ((rationalModel i).map (Rat.castHom (Padic 2))).c₄=exp (-4 : ℤ) ∧
    valuation (Padic 2) (maximalIdeal (PadicInt 2))
      ((rationalModel i).map (Rat.castHom (Padic 2))).Δ=exp (-(twoExponent i : ℤ)) := by
  have h := And.intro (c4_value_two i) (discriminant_value_two i)
  simpa only [localModel_eq] using h

theorem ec_reduction_types (p : ℕ) [Fact p.Prime] :
    (HasGoodReduction (PadicInt p) (EC.map (Rat.castHom (Padic p))) ↔
      p ∉ ({2,3,5,7,11} : Finset ℕ)) ∧
    (HasMultiplicativeReduction (PadicInt p) (EC.map (Rat.castHom (Padic p))) ↔
      p ∈ ({2,3,5,7,11} : Finset ℕ) ∧ p≠2) ∧
    (HasAdditiveReduction (PadicInt p) (EC.map (Rat.castHom (Padic p))) ↔ p=2) := by
  simpa [rationalModel,badPrimes] using model_reduction_types 0 p

theorem jg_reduction_types (p : ℕ) [Fact p.Prime] :
    (HasGoodReduction (PadicInt p) (JG.map (Rat.castHom (Padic p))) ↔
      p ∉ ({2,3,5,7,11,37} : Finset ℕ)) ∧
    (HasMultiplicativeReduction (PadicInt p) (JG.map (Rat.castHom (Padic p))) ↔
      p ∈ ({2,3,5,7,11,37} : Finset ℕ) ∧ p≠2) ∧
    (HasAdditiveReduction (PadicInt p) (JG.map (Rat.castHom (Padic p))) ↔ p=2) := by
  simpa [rationalModel,badPrimes] using model_reduction_types 1 p

theorem j2_reduction_types (p : ℕ) [Fact p.Prime] :
    (HasGoodReduction (PadicInt p) (J2.map (Rat.castHom (Padic p))) ↔
      p ∉ ({2,3,5,7,11,17,19,23,29,197,233} : Finset ℕ)) ∧
    (HasMultiplicativeReduction (PadicInt p) (J2.map (Rat.castHom (Padic p))) ↔
      p ∈ ({2,3,5,7,11,17,19,23,29,197,233} : Finset ℕ) ∧ p≠2) ∧
    (HasAdditiveReduction (PadicInt p) (J2.map (Rat.castHom (Padic p))) ↔ p=2) := by
  simpa [rationalModel,badPrimes] using model_reduction_types 2 p

end
end Z2Z4Rank6.PrintedModelReduction
