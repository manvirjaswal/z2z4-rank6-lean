import Z2Z4Rank6.ECFullSupportRefinement
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.BigOperators.Associated

/-!
# Exact prime-bit coordinates for canonical squarefree covering coefficients

A squarefree divisor of a finite distinct-prime product is exactly the
product of the primes which divide it. This is integer factorization,
with no finite search over a large prime pool. The parity theorem records
the square-product relation for canonical split two-coverings.
-/

namespace Z2Z4Rank6.SplitPrimeBits

open scoped BigOperators

/-- Exact prime-bit factorization of a squarefree supported natural number. -/
theorem factorization {n : ℕ} (ps : Fin n → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (m : ℕ) (hm : Squarefree m) (hdiv : m∣∏ i, ps i) :
    m=∏ i, (ps i)^(if ps i∣m then 1 else 0) := by
  classical
  let t : Finset (Fin n) := Finset.univ.filter (fun i => ps i∣m)
  have himage : t.image ps=m.primeFactors := by
    ext p
    constructor
    · rintro hp
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
      exact (hprime i).mem_primeFactors (Finset.mem_filter.mp hi).2 hm.ne_zero
    · intro hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpdiv : p∣∏ i, ps i := (Nat.dvd_of_mem_primeFactors hp).trans hdiv
      obtain ⟨i,_,hpi⟩ := ((Nat.prime_iff.mp hpprime).dvd_finsetProd_iff ps).mp hpdiv
      have he : p=ps i := (Nat.prime_dvd_prime_iff_eq hpprime (hprime i)).mp hpi
      refine Finset.mem_image.mpr ⟨i,?_,he.symm⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,he ▸ Nat.dvd_of_mem_primeFactors hp⟩
  calc
    m=∏ p∈m.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hm).symm
    _=∏ i∈t, ps i := by
      rw [← himage,Finset.prod_image]
      exact fun _ _ _ _ h => hinj h
    _=∏ i, (ps i)^(if ps i∣m then 1 else 0) := by
      dsimp only [t]
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : ps i∣m <;> simp [h]

/-- A power in the support bound does not change squarefree prime bits. -/
theorem factorization_of_dvd_pow {n : ℕ} (ps : Fin n → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (m k : ℕ) (hm : Squarefree m) (hdiv : m∣(∏ i, ps i)^k) :
    m=∏ i, (ps i)^(if ps i∣m then 1 else 0) := by
  apply factorization ps hinj hprime m hm
  by_cases hk : k=0
  · subst k
    have hm1 : m=1 := Nat.dvd_one.mp (by simpa using hdiv)
    simp [hm1]
  · exact (hm.dvd_pow_iff_dvd hk).mp hdiv

/-- The same exact bit factorization for the absolute value of a canonical
squarefree integer coefficient. -/
theorem natAbs_factorization_of_dvd_pow {n : ℕ} (ps : Fin n → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ℤ) (k : ℕ) (hd : Squarefree d) (hdiv : d.natAbs∣(∏ i, ps i)^k) :
    d.natAbs=∏ i, (ps i)^(if (ps i : ℤ)∣d then 1 else 0) := by
  simpa only [Int.natCast_dvd] using
    factorization_of_dvd_pow ps hinj hprime d.natAbs k (Int.squarefree_natAbs.mpr hd) hdiv

/-- The three prime-divisibility bits of a squarefree square-product
triple sum to zero in F₂. -/
theorem square_product_parity {p : ℕ} [Fact p.Prime]
    (d1 d2 d3 : ℤ) (hs1 : Squarefree d1) (hs2 : Squarefree d2) (hs3 : Squarefree d3)
    (hsq : IsSquare (d1*d2*d3)) :
    (if (p : ℤ)∣d1 then 1 else 0 : ZMod 2)+
      (if (p : ℤ)∣d2 then 1 else 0)+
      (if (p : ℤ)∣d3 then 1 else 0)=0 := by
  by_cases h1 : (p : ℤ)∣d1
  · rcases squarefree_product_prime_parity d1 d2 d3 hs1 hs2 hs3 hsq h1 with h | h
    · norm_num [h1,h.1,h.2]; decide +kernel
    · norm_num [h1,h.1,h.2]; decide +kernel
  · by_cases h2 : (p : ℤ)∣d2
    · have hsq' : IsSquare (d2*d1*d3) := by simpa only [mul_comm d1 d2] using hsq
      rcases squarefree_product_prime_parity d2 d1 d3 hs2 hs1 hs3 hsq' h2 with h | h
      · exact False.elim (h1 h.1)
      · norm_num [h1,h2,h.2]; decide +kernel
    · by_cases h3 : (p : ℤ)∣d3
      · have hsq' : IsSquare (d3*d1*d2) := by convert hsq using 1; ring
        rcases squarefree_product_prime_parity d3 d1 d2 hs3 hs1 hs2 hsq' h3 with h | h
        · exact False.elim (h1 h.1)
        · exact False.elim (h2 h.2)
      · simp [h1,h2,h3]

end Z2Z4Rank6.SplitPrimeBits
