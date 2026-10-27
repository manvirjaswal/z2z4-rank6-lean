import Z2Z4Rank6.PrintedModelConductorComponents

/-!
# Exact geometric conductors of EC, JG and J2

The conductor uses minimal proper regular models and geometric special
fibers. All integer factorizations, translations and valuation conditions are
proved. The two local-component hypotheses are specializations of Mulholland's theorems. The result
is independent of the supplied model data.
-/

namespace Z2Z4Rank6.PrintedModelConductorValues
noncomputable section
open Common.Elliptic GeometricConductor MulhollandModelTheorems
open PrintedModelMinimality PrintedModelReduction PrintedModelConductorComponents
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem discriminant_natVal (i : Fin 3) (p : ℕ) [Fact p.Prime] :
    padicValNat p (integerModel i).Δ.natAbs = discriminantExponent i p := by
  by_cases hp : p ∈ badPrimes i
  · obtain ⟨hf,hu⟩ := discriminant_residual_certificate i p hp
    have hΔ : (integerModel i).Δ =
        (p:ℤ)^discriminantExponent i p*discriminantResidual i p :=
      (discriminant_factorization i).trans hf
    have hn : ¬p ∣ (discriminantResidual i p).natAbs := by
      simpa only [Int.natCast_dvd] using hu
    have hr : (discriminantResidual i p).natAbs ≠ 0 := by
      intro h
      apply hn
      rw [h]
      exact dvd_zero _
    rw [hΔ,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast,
      padicValNat.mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hr,
      padicValNat.prime_pow,padicValNat.eq_zero_of_not_dvd hn,add_zero]
  · have hn : ¬p ∣ (integerModel i).Δ.natAbs := by
      rw [←Int.natCast_dvd,prime_dvd_discriminant_iff]
      exact hp
    rw [padicValNat.eq_zero_of_not_dvd hn,discriminantExponent_eq_zero_of_not_mem i p hp]

theorem primeFactors_eq (i : Fin 3) : (integerModel i).Δ.natAbs.primeFactors = badPrimes i := by
  ext p
  constructor
  · intro hp
    have hprime := (Nat.mem_primeFactors.mp hp).1
    let : Fact p.Prime := ⟨hprime⟩
    apply (prime_dvd_discriminant_iff i p).mp
    exact Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hp).2.1
  · intro hp
    have hall (j : Fin 3) : ∀ q ∈ badPrimes j, q.Prime := by
      fin_cases j <;> norm_num [badPrimes]
    have hprime : p.Prime := hall i p hp
    let : Fact p.Prime := ⟨hprime⟩
    refine Nat.mem_primeFactors.mpr ⟨hprime,?_,?_⟩
    · exact Int.natCast_dvd.mp ((prime_dvd_discriminant_iff i p).mpr hp)
    · exact Int.natAbs_ne_zero.mpr (PrintedModelConductorData.discriminant_ne_zero i)

def twoConductorExponent : Fin 3 → ℕ := ![3,4,4]
def printedConductor : Fin 3 → ℕ := ![9240,683760,182747931661680]

theorem exponent_two (h21 : Theorem21Components) (i : Fin 3) (D : Data (integerModel i)) :
    D.exponent 2 = twoConductorExponent i := by
  rw [Data.exponent,componentCount_two h21,discriminant_natVal]
  fin_cases i <;> norm_num [discriminantExponent,PrintedModelRootTranslations.starIndex,twoConductorExponent]

theorem exponent_odd (hOdd : Theorems23And24SemistableComponents)
    (i : Fin 3) (D : Data (integerModel i)) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    D.exponent p = if p ∈ badPrimes i then 1 else 0 := by
  rw [Data.exponent,componentCount_odd hOdd i D p hp]
  by_cases hd : p ∣ (integerModel i).Δ.natAbs
  · have hb : p ∈ badPrimes i :=
      (prime_dvd_discriminant_iff i p).mp (Int.natCast_dvd.mpr hd)
    simp [hd,hb]
  · have hb : p ∉ badPrimes i := by
      intro h
      exact hd (Int.natCast_dvd.mp ((prime_dvd_discriminant_iff i p).mpr h))
    simp [hd,hb,padicValNat.eq_zero_of_not_dvd hd]

theorem conductor_eq (h21 : Theorem21Components)
    (hOdd : Theorems23And24SemistableComponents) (i : Fin 3) (D : Data (integerModel i)) :
    D.conductor = printedConductor i := by
  have hfactor (p : ℕ) (hp : p ∈ badPrimes i) :
      D.factor p = p^(if p=2 then twoConductorExponent i else 1) := by
    have hprime : p.Prime := (Nat.mem_primeFactors.mp (by rwa [primeFactors_eq])).1
    let : Fact p.Prime := ⟨hprime⟩
    rw [Data.factor_eq_prime_pow]
    by_cases h2 : p=2
    · subst p
      rw [exponent_two h21]
      simp
    · rw [exponent_odd hOdd i D p h2]
      simp [h2,hp]
  calc
    D.conductor = ∏p ∈ badPrimes i,p^(if p=2 then twoConductorExponent i else 1) := by
      rw [Data.conductor,primeFactors_eq]
      exact Finset.prod_congr rfl hfactor
    _ = printedConductor i := by
      fin_cases i <;> norm_num [badPrimes,twoConductorExponent,printedConductor]

end
end Z2Z4Rank6.PrintedModelConductorValues
