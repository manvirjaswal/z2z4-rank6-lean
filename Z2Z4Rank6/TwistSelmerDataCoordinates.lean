module

public import Z2Z4Rank6.TwistSelmerData
public import Z2Z4Rank6.SplitPrimeBits
public import Z2Z4Rank6.SplitRealConditions
public import Z2Z4Rank6.SplitTwistPrimeConditions

@[expose] public section

/-!
# Canonical integer covering coefficients in prime bits

Exact signed reconstruction from the canonical squarefree representatives,
for the finite split two-descent certificates in Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117. The bits record prime divisibility.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

def coefficient (d : ECFullTriple) : Fin 3 → ℤ := ![d.1,d.2.1,d.2.2]
def signBit (d : ℤ) : ZMod 2 := if d<0 then 1 else 0
def primeBit (p : ℕ) (d : ℤ) : ZMod 2 := if (p : ℤ)∣d then 1 else 0

def primeProduct {s : ℕ} (ps : Fin s → ℕ) (v : Fin s → ZMod 2) : ℤ :=
  ∏ i, (ps i : ℤ)^(v i).val

@[simp] theorem bit_one_val : (1 : ZMod 2).val=1 := by decide +kernel

@[simp] theorem primeBit_val (p : ℕ) (d : ℤ) :
    (primeBit p d).val=if (p : ℤ)∣d then 1 else 0 := by
  by_cases h : (p : ℤ)∣d <;> norm_num [primeBit,h]

@[simp] theorem signBit_val (d : ℤ) : (signBit d).val=if d<0 then 1 else 0 := by
  by_cases h : d<0 <;> norm_num [signBit,h]

theorem signed_prime_factorization {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ℤ) (k : ℕ) (hd : Squarefree d) (hdiv : d.natAbs∣(∏ i, ps i)^k) :
    d=(-1)^(signBit d).val*primeProduct ps (fun i => primeBit (ps i) d) := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (SplitPrimeBits.natAbs_factorization_of_dvd_pow ps hinj hprime d k hd hdiv)
  simp only [Nat.cast_prod,Nat.cast_pow,Int.natCast_natAbs] at h
  simp_rw [←primeBit_val] at h
  change |d|=primeProduct ps (fun i => primeBit (ps i) d) at h
  rw [←h]
  by_cases hn : d<0
  · simp [signBit,hn,abs_of_neg hn]
  · simp [signBit,hn,abs_of_nonneg (le_of_not_gt hn)]

/-- A square-product triple with positive second coordinate has equal first
and third signs. -/
theorem first_third_signBit_eq (d : ECFullTriple)
    (h1 : d.1≠0) (h3 : d.2.2≠0) (h2 : 0<d.2.1)
    (hsq : IsSquare (d.1*d.2.1*d.2.2)) : signBit d.1=signBit d.2.2 := by
  have hp : 0≤d.1*d.2.1*d.2.2 := by
    obtain ⟨t,ht⟩ := hsq
    rw [ht]
    exact mul_self_nonneg _
  by_cases hn : d.1<0
  · have h12 : d.1*d.2.1<0 := mul_neg_of_neg_of_pos hn h2
    have h3nonpos : d.2.2≤0 := by
      rcases mul_nonneg_iff.mp hp with h | h
      · exact False.elim (h12.not_ge h.1)
      · exact h.2
    have h3neg : d.2.2<0 := lt_of_le_of_ne h3nonpos h3
    simp [signBit,hn,h3neg]
  · have h1pos : 0<d.1 := lt_of_le_of_ne (le_of_not_gt hn) h1.symm
    have h12 : 0<d.1*d.2.1 := mul_pos h1pos h2
    have h3nonneg : 0≤d.2.2 := (mul_nonneg_iff_of_pos_left h12).mp hp
    simp [signBit,hn,not_lt_of_ge h3nonneg]

abbrev BitDimension (s : ℕ) := 3*s+1

def rawIndex {s : ℕ} (c : Fin 3) (i : Fin s) : Fin (BitDimension s) :=
  (finProdFinEquiv (c,i)).succ

/-- The sign and prime-divisibility bits, with no choice of square roots. -/
def bitVector {s : ℕ} (ps : Fin s → ℕ) (d : ECFullTriple) :
    Fin (BitDimension s) → ZMod 2 :=
  Fin.cons (signBit d.1) (fun j =>
    primeBit (ps (finProdFinEquiv.symm j).2) (coefficient d (finProdFinEquiv.symm j).1))

@[simp] theorem bitVector_zero {s : ℕ} (ps : Fin s → ℕ) (d : ECFullTriple) :
    bitVector ps d 0=signBit d.1 := rfl

@[simp] theorem bitVector_rawIndex {s : ℕ} (ps : Fin s → ℕ)
    (d : ECFullTriple) (c : Fin 3) (i : Fin s) :
    bitVector ps d (rawIndex c i)=primeBit (ps i) (coefficient d c) := by
  change primeBit (ps ((finProdFinEquiv).symm (finProdFinEquiv (c,i))).2)
    (coefficient d ((finProdFinEquiv).symm (finProdFinEquiv (c,i))).1)=_
  simp only [Equiv.symm_apply_apply]

/-- Recover all three canonical integer representatives from raw bits. -/
def candidate {s : ℕ} (ps : Fin s → ℕ) (v : Fin (BitDimension s) → ZMod 2) : ECFullTriple :=
  ((-1)^(v 0).val*primeProduct ps (fun i => v (rawIndex 0 i)),
    primeProduct ps (fun i => v (rawIndex 1 i)),
    (-1)^(v 0).val*primeProduct ps (fun i => v (rawIndex 2 i)))

theorem candidate_bitVector {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ECFullTriple) (k : ℕ) (hs : ∀ c, Squarefree (coefficient d c))
    (hdiv : ∀ c, (coefficient d c).natAbs∣(∏ i, ps i)^k)
    (hpos : 0<d.2.1) (hsq : IsSquare (d.1*d.2.1*d.2.2)) :
    candidate ps (bitVector ps d)=d := by
  have h1 := signed_prime_factorization ps hinj hprime d.1 k (hs 0) (hdiv 0)
  have h2 := signed_prime_factorization ps hinj hprime d.2.1 k (hs 1) (hdiv 1)
  have h3 := signed_prime_factorization ps hinj hprime d.2.2 k (hs 2) (hdiv 2)
  have hsgn := first_third_signBit_eq d (hs 0).ne_zero (hs 2).ne_zero hpos hsq
  have h2sgn : signBit d.2.1=0 := by simp [signBit,not_lt_of_gt hpos]
  apply Prod.ext
  · simpa [candidate,coefficient] using h1.symm
  · apply Prod.ext
    · simpa [candidate,coefficient,h2sgn] using h2.symm
    · simpa [candidate,coefficient,hsgn] using h3.symm

end
end Z2Z4Rank6.TwistSelmer
