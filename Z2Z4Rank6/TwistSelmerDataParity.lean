import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Quadratic-character parity and exact linear constraints

Multiplicativity of the finite-field quadratic character converts the
odd-prime square conditions on split covering coefficients into linear
relations over ZMod 2. Concrete tables use Euler's criterion, not enumeration
of field square roots. This supports Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

/-- Square class parity in a finite field: zero for a square, one otherwise. -/
def squareParity {F : Type*} [Field F] [Fintype F] (a : F) : ZMod 2 := by
  classical
  exact if IsSquare a then 0 else 1

theorem squareParity_eq_zero_iff {F : Type*} [Field F] [Fintype F] (a : F) :
    squareParity a=0 ↔ IsSquare a := by
  classical
  simp [squareParity]

/-- Quadratic parity is additive under multiplication of nonzero factors. -/
theorem squareParity_mul {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b : F) (ha : a≠0) (hb : b≠0) :
    squareParity (a*b)=squareParity a+squareParity b := by
  classical
  unfold squareParity
  simp only [←quadraticChar_one_iff_isSquare (mul_ne_zero ha hb),
    ←quadraticChar_one_iff_isSquare ha,←quadraticChar_one_iff_isSquare hb,map_mul]
  rcases quadraticChar_dichotomy ha with h | h <;>
    rcases quadraticChar_dichotomy hb with h' | h'
  all_goals norm_num [h,h']
  decide +kernel

theorem squareParity_pow {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a : F) (n : ℕ) (ha : a≠0) : squareParity (a^n)=n • squareParity a := by
  induction n with
  | zero => simp [squareParity]
  | succ n ih => rw [pow_succ,squareParity_mul _ _ (pow_ne_zero n ha) ha,ih,succ_nsmul]

theorem squareParity_prod {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    (s : Finset ι) (f : ι → F) (hf : ∀ i∈s, f i≠0) :
    squareParity (∏ i∈s, f i)=∑ i∈s, squareParity (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [squareParity]
  | @insert i s hi ih =>
    have hs : ∀ j∈s, f j≠0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,
      squareParity_mul _ _ (hf i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs),ih hs]

/-- Bit exponents give exactly the associated F₂ linear form. -/
theorem squareParity_product_powers {F ι : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] (f : ι → F) (b : ι → ZMod 2) (hf : ∀ i, f i≠0) :
    squareParity (∏ i, (f i)^(b i).val)=∑ i, b i*squareParity (f i) := by
  rw [squareParity_prod Finset.univ _ (fun i _ => pow_ne_zero _ (hf i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [squareParity_pow _ _ (hf i),nsmul_eq_mul,ZMod.natCast_zmod_val]

end

/-- Computable quadratic parity, using Euler's criterion for a prime modulus. -/
def modularParity (p : ℕ) (n : ℤ) : ZMod 2 :=
  if (n : ZMod p)=0 ∨ (n : ZMod p)^(p/2)=1 then 0 else 1

noncomputable section

theorem modularParity_eq_squareParity (p : ℕ) [Fact p.Prime] (n : ℤ) :
    modularParity p n=squareParity (n : ZMod p) := by
  classical
  by_cases h : (n : ZMod p)=0
  · simp [modularParity,squareParity,h]
  · simp only [modularParity,squareParity,h,false_or]
    simp only [ZMod.euler_criterion p h]

theorem modularParity_eq_zero_iff (p : ℕ) [Fact p.Prime] (n : ℤ) :
    modularParity p n=0 ↔ IsSquare (n : ZMod p) := by
  rw [modularParity_eq_squareParity,squareParity_eq_zero_iff]

theorem modularParity_product_powers {ι : Type*} [Fintype ι]
    (p : ℕ) [Fact p.Prime] (f : ι → ℤ) (b : ι → ZMod 2)
    (hf : ∀ i, (f i : ZMod p)≠0) :
    modularParity p (∏ i, (f i)^(b i).val)=∑ i, b i*modularParity p (f i) := by
  simp_rw [modularParity_eq_squareParity]
  push_cast
  exact squareParity_product_powers _ b hf

theorem modularParity_mul (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : (a : ZMod p)≠0) (hb : (b : ZMod p)≠0) :
    modularParity p (a*b)=modularParity p a+modularParity p b := by
  simp_rw [modularParity_eq_squareParity]
  push_cast
  exact squareParity_mul _ _ ha hb

theorem modularParity_one (p : ℕ) [Fact p.Prime] : modularParity p 1=0 := by
  apply (modularParity_eq_zero_iff p 1).mpr
  exact ⟨(1 : ZMod p),by simp⟩

theorem modularParity_if (p : ℕ) [Fact p.Prime] (a d : ℤ) :
    modularParity p (if (p : ℤ)∣d then a else 1)=
      (if (p : ℤ)∣d then 1 else 0 : ZMod 2)*modularParity p a := by
  by_cases hd : (p : ℤ)∣d <;> simp [hd,modularParity_one]


theorem modularParity_pow (p : ℕ) [Fact p.Prime] (a : ℤ) (n : ℕ)
    (ha : (a : ZMod p)≠0) :
    modularParity p (a^n)=(n : ZMod 2)*modularParity p a := by
  simp_rw [modularParity_eq_squareParity]
  push_cast
  rw [squareParity_pow _ _ ha,nsmul_eq_mul]


end
end Z2Z4Rank6.TwistSelmer
