module

public import Z2Z4Rank6.GusicTadicIrreducible
public import Z2Z4Rank6.GusicTadicCandidates
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Ring.Int.Units

@[expose] public section

/-!
# Divisors of the specialization factor pools

The polynomial-divisor step in Propositions 2.3 and 5.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117. A divisor of a product of irreducibles
is associated to a binary subproduct. The only units of ℤ[m] are ±1, so the
sign class already present in each pool gives an exact binary representation.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
open scoped BigOperators
noncomputable section

/-- Divisors of a finite irreducible product are associated to binary subproducts. -/
theorem divisor_irreducible_product {n : ℕ} (f : Fin n → ℤ[X])
    (hf : ∀ i, Irreducible (f i)) (g : ℤ[X]) (hg : g ∣ ∏ i, f i) :
    ∃ b : Fin n → Fin 2, Associated g (∏ i, f i^(b i).val) := by
  induction n generalizing g with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, ?_⟩
    simp only [Fin.prod_univ_zero] at hg ⊢
    exact associated_one_iff_isUnit.mpr (isUnit_of_dvd_one hg)
  | succ n ih =>
    rw [Fin.prod_univ_succ] at hg
    obtain ⟨d,e,hd,he,hg⟩ := exists_dvd_and_dvd_of_dvd_mul hg
    obtain ⟨b,hb⟩ := ih (fun i => f i.succ) (fun i => hf i.succ) e he
    rcases (hf 0).dvd_iff.mp hd with hu | ha
    · refine ⟨Fin.cons 0 b, ?_⟩
      rw [hg]
      have hh := (associated_one_iff_isUnit.mpr hu).mul_mul hb
      simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
        pow_zero, one_mul] using hh
    · refine ⟨Fin.cons 1 b, ?_⟩
      rw [hg]
      have hh := ha.symm.mul_mul hb
      simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_one,
        pow_one] using hh

/-- Associated integer polynomials differ by a sign. -/
theorem associated_polynomial_eq_or_neg {p q : ℤ[X]} (h : Associated p q) : p=q ∨ p= -q := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨r,hr,hru⟩ := Polynomial.isUnit_iff.mp u.isUnit
  rcases Int.isUnit_eq_one_or hr with hr | hr
  · subst r
    have he : (u : ℤ[X])=1 := by simpa only [C_1] using hru.symm
    left
    simpa only [he, mul_one] using hu
  · subst r
    have he : (u : ℤ[X])= -1 := by simpa only [C_neg, C_1] using hru.symm
    right
    rw [he, mul_neg_one] at hu
    simpa only [neg_neg] using congrArg Neg.neg hu

/-- Adding the last factor −1 turns associated subproduct representations into exact ones. -/
theorem divisor_binary_representation {n : ℕ} (f : Fin (n+1) → ℤ[X])
    (hf : ∀ i : Fin n, Irreducible (f i.castSucc)) (hsign : f (Fin.last n)= -1)
    (g : ℤ[X]) (hg : g ∣ ∏ i : Fin n, f i.castSucc) :
    ∃ b : Fin (n+1) → Fin 2, g=∏ i, f i^(b i).val := by
  obtain ⟨b,hb⟩ := divisor_irreducible_product (fun i => f i.castSucc) hf g hg
  rcases associated_polynomial_eq_or_neg hb with hg | hg
  · refine ⟨Fin.snoc b 0, ?_⟩
    simpa only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_zero, pow_zero, mul_one] using hg
  · refine ⟨Fin.snoc b 1, ?_⟩
    simpa only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.val_one, pow_one, hsign, mul_neg_one] using hg

/-- The exact binary representation returns to the printed order by the explicit permutation. -/
theorem binary_representation_unpermute {n : ℕ} (f : Fin n → ℤ[X]) (e : Equiv.Perm (Fin n))
    (g : ℤ[X]) (h : ∃ b : Fin n → Fin 2, g=∏ i, f (e i)^(b i).val) :
    ∃ b : Fin n → Fin 2, g=∏ i, f i^(b i).val := by
  obtain ⟨b,hb⟩ := h
  refine ⟨fun i => b (e.symm i), ?_⟩
  rw [hb]
  simpa only [e.symm_apply_apply] using
    (Equiv.prod_comp e (fun i => f i^(b (e.symm i)).val))

end

end Z2Z4Rank6.GusicTadic
