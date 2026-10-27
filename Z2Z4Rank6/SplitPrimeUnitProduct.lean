import Z2Z4Rank6.TwistSelmerDataCoordinates

/-!
# Exact unit parts of signed squarefree prime products

The canonical integer coefficients used in the twist certificates
of Proposition 5.2, Jaswal, DOI: 10.5281/zenodo.23437117, are reconstructed
from their sign and prime-divisibility bits. This module removes the chosen
prime from that reconstruction and proves that every remaining factor is
nonzero in its residue field.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

def unitPrimeFactor (p q : ℕ) : ℤ := if q=p then 1 else q

def unitPrimeProduct {s : ℕ} (p : ℕ) (ps : Fin s → ℕ) (v : Fin s → ZMod 2) : ℤ :=
  ∏ i, unitPrimeFactor p (ps i)^(v i).val

theorem primeProduct_decompose {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (v : Fin s → ZMod 2) (j : Fin s) :
    primeProduct ps v=(ps j : ℤ)^(v j).val*unitPrimeProduct (ps j) ps v := by
  have hU : unitPrimeProduct (ps j) ps v =
      ∏ i ∈ Finset.univ.erase j, (ps i : ℤ)^(v i).val := by
    unfold unitPrimeProduct
    rw [←Finset.mul_prod_erase Finset.univ
      (fun i => unitPrimeFactor (ps j) (ps i)^(v i).val) (Finset.mem_univ j)]
    simp only [unitPrimeFactor,ite_true,one_pow,one_mul]
    apply Finset.prod_congr rfl
    intro i hi
    have hij : ps i ≠ ps j := fun he => (Finset.mem_erase.mp hi).1 (hinj he)
    rw [ite_eq_right hij]
  rw [primeProduct,hU]
  exact (Finset.mul_prod_erase Finset.univ (fun i => (ps i : ℤ)^(v i).val)
    (Finset.mem_univ j)).symm

/-- Removing p from the signed reconstruction gives the exact integer unit
part, rather than just an equality of square classes. -/
theorem unitPart_signed_prime_factorization {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ℤ) (k : ℕ) (hd : Squarefree d) (hdiv : d.natAbs∣(∏ i, ps i)^k)
    (j : Fin s) :
    SplitTwistPrime.unitPart (ps j) d =
      (-1)^(signBit d).val*unitPrimeProduct (ps j) ps (fun i => primeBit (ps i) d) := by
  have hf := signed_prime_factorization ps hinj hprime d k hd hdiv
  rw [primeProduct_decompose ps hinj _ j] at hf
  by_cases hp : (ps j : ℤ)∣d
  · rw [primeBit_val,ite_eq_left hp,pow_one] at hf
    rw [SplitTwistPrime.unitPart,ite_eq_left hp]
    conv_lhs => rw [hf]
    have hp0 : (ps j : ℤ) ≠ 0 := by exact_mod_cast (hprime j).ne_zero
    rw [←mul_assoc,mul_comm _ (ps j : ℤ),mul_assoc]
    exact Int.mul_ediv_cancel_left _ hp0
  · rw [primeBit_val,ite_eq_right hp,pow_zero,one_mul] at hf
    rw [SplitTwistPrime.unitPart,ite_eq_right hp]
    exact hf

theorem unitPrimeFactor_cast_ne_zero (p q : ℕ) [Fact p.Prime] (hq : q.Prime) :
    (unitPrimeFactor p q : ZMod p) ≠ 0 := by
  by_cases hqp : q=p
  · simp [unitPrimeFactor,hqp]
  · simp only [unitPrimeFactor,ite_eq_right hqp,Int.cast_natCast]
    intro hz
    have hpqi : (p : ℤ) ∣ (q : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa only [Int.cast_natCast] using hz)
    have hpq : p ∣ q := by exact_mod_cast hpqi
    exact hqp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hq).mp hpq).symm

theorem unitPrimeProduct_cast_ne_zero {s : ℕ} (p : ℕ) [Fact p.Prime]
    (ps : Fin s → ℕ) (hprime : ∀ i, (ps i).Prime) (v : Fin s → ZMod 2) :
    (unitPrimeProduct p ps v : ZMod p) ≠ 0 := by
  simp only [unitPrimeProduct,Int.cast_prod,Int.cast_pow]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (unitPrimeFactor_cast_ne_zero p (ps i) (hprime i))

end
end Z2Z4Rank6.TwistSelmer
