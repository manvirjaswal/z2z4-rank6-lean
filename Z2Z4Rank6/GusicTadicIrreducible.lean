import Z2Z4Rank6.GusicTadicQuartic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Irreducibility of the specialization factor pools

The nonconstant factors in Propositions 2.3 and 5.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117. The quadratic tests are the rational
nonsquare test for 99 and positivity for 3m²+242 and 2m²+243. The quartic
factor is treated in GusicTadicQuartic.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
noncomputable section

local notation "T" => (Polynomial.X : ℤ[X])
local notation "U" => (Polynomial.X : ℚ[X])

theorem quadraticQ_irreducible : Irreducible (U^2-99) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (U^2-99).natDegree=2 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have hs : ¬IsSquare (99 : ℚ) := by norm_num
    apply hs
    refine ⟨x, ?_⟩
    have he : x^2-99=0 := by simpa only [IsRoot, eval_sub, eval_pow, eval_X, eval_ofNat] using hx
    nlinarith

theorem q1CoreQ_irreducible : Irreducible (3*U^2+242) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (3*U^2+242).natDegree=2 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have he : 3*x^2+242=0 := by
      simpa only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat] using hx
    nlinarith [sq_nonneg x]

theorem q2CoreQ_irreducible : Irreducible (2*U^2+243) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (2*U^2+243).natDegree=2 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have he : 2*x^2+243=0 := by
      simpa only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat] using hx
    nlinarith [sq_nonneg x]

theorem quadraticFactor_irreducible : Irreducible quadraticFactor := by
  have hp := isPrimitive_iff_content_eq_one.mpr quadraticFactor_content
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).2
  simpa [quadraticFactor] using quadraticQ_irreducible

theorem q1Core_irreducible : Irreducible (3*T^2+242) := by
  have hp := isPrimitive_iff_content_eq_one.mpr q1Core_content
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).2
  simpa using q1CoreQ_irreducible

theorem q2Core_irreducible : Irreducible (2*T^2+243) := by
  have hp := isPrimitive_iff_content_eq_one.mpr q2Core_content
  apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp).2
  simpa using q2CoreQ_irreducible

/-- Every one of the eleven listed integer polynomial factors is irreducible. -/
theorem baseFactors_irreducible (i : Fin 11) : Irreducible (baseFactors T i) := by
  fin_cases i
  · simpa [baseFactors] using irreducible_X_sub_C (99 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (-1 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (11 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (-9 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (-99 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (1 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (-11 : ℤ)
  · simpa [baseFactors] using irreducible_X_sub_C (9 : ℤ)
  · simpa [baseFactors] using (irreducible_X : Irreducible T)
  · exact quadraticFactor_irreducible
  · exact quarticFactor_irreducible

/-- The content primes are irreducible as constant integer polynomials. -/
theorem contentPrime_irreducible (p : ℕ) (hp : p.Prime) : Irreducible (C (p : ℤ)) := by
  apply Prime.irreducible
  apply Polynomial.prime_C_iff.mpr
  exact Nat.prime_iff_prime_int.mp hp

end

end Z2Z4Rank6.GusicTadic
