module

public import Z2Z4Rank6.TwistSelmerDataParity
public import Z2Z4Rank6.SplitPrimeUnitProduct
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# Covering constraints as binary matrix rows

Each character row is the quadratic character of a canonical
covering coefficient's unit part. Exact prime factorization and proved
character multiplicativity connect it to the finite matrix certificate.
This is the arithmetic compression used for Jaswal, Proposition 5.2,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

def selectorRow {n : ℕ} (i : Fin n) : Fin n → ZMod 2 := Pi.single i 1

@[simp] theorem selectorRow_dot {n : ℕ} (i : Fin n) (v : Fin n → ZMod 2) :
    selectorRow i ⬝ᵥ v=v i := single_one_dotProduct i v

def signWeight (c : Fin 3) (p : ℕ) : ZMod 2 :=
  if c=1 then 0 else modularParity p (-1)

/-- The exact quadratic-character row for a signed unit coefficient. -/
def characterRow {s : ℕ} (ps : Fin s → ℕ) (c : Fin 3) (p : ℕ) :
    Fin (BitDimension s) → ZMod 2 :=
  signWeight c p • selectorRow 0+
    ∑ i, modularParity p (unitPrimeFactor p (ps i)) • selectorRow (rawIndex c i)

theorem characterRow_dot {s : ℕ} (ps : Fin s → ℕ) (c : Fin 3) (p : ℕ)
    (v : Fin (BitDimension s) → ZMod 2) :
    characterRow ps c p ⬝ᵥ v=signWeight c p*v 0+
      ∑ i, modularParity p (unitPrimeFactor p (ps i))*v (rawIndex c i) := by
  simp [characterRow,add_dotProduct,sum_dotProduct,smul_dotProduct,smul_eq_mul]

theorem coefficient_signBit (d : ECFullTriple) (c : Fin 3)
    (h1 : d.1≠0) (h3 : d.2.2≠0) (h2 : 0<d.2.1)
    (hsq : IsSquare (d.1*d.2.1*d.2.2)) :
    signBit (coefficient d c)=if c=1 then 0 else signBit d.1 := by
  fin_cases c
  · rfl
  · simp [coefficient,signBit,not_lt_of_gt h2]
  · simpa [coefficient] using (first_third_signBit_eq d h1 h3 h2 hsq).symm

/-- Unit-part parity equals its linear row on sign/divisibility
bits. No abstract bit vector is substituted for the canonical coefficient. -/
theorem characterRow_source {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ECFullTriple) (k : ℕ) (hs : ∀ c, Squarefree (coefficient d c))
    (hdiv : ∀ c, (coefficient d c).natAbs∣(∏ i, ps i)^k)
    (hpos : 0<d.2.1) (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (c : Fin 3) (j : Fin s) :
    characterRow ps c (ps j) ⬝ᵥ bitVector ps d=
      modularParity (ps j) (SplitTwistPrime.unitPart (ps j) (coefficient d c)) := by
  let : Fact (ps j).Prime := ⟨hprime j⟩
  have hU := unitPart_signed_prime_factorization ps hinj hprime (coefficient d c) k (hs c) (hdiv c) j
  have hn : (((-1 : ℤ) : ZMod (ps j)))≠0 := by simp
  have hnPow : (((-1 : ℤ)^(signBit (coefficient d c)).val : ℤ) : ZMod (ps j))≠0 := by
    rw [Int.cast_pow]
    exact pow_ne_zero _ hn
  have hprod := modularParity_product_powers (ps j) (fun i => unitPrimeFactor (ps j) (ps i))
    (fun i => primeBit (ps i) (coefficient d c))
    (fun i => unitPrimeFactor_cast_ne_zero (ps j) (ps i) (hprime i))
  change modularParity (ps j) (unitPrimeProduct (ps j) ps
    (fun i => primeBit (ps i) (coefficient d c)))=_ at hprod
  rw [hU,modularParity_mul _ _ _ hnPow
    (unitPrimeProduct_cast_ne_zero (ps j) ps hprime _),
    modularParity_pow _ _ _ hn,hprod,ZMod.natCast_zmod_val]
  rw [characterRow_dot]
  simp only [bitVector_zero,bitVector_rawIndex]
  have hsign := coefficient_signBit d c (hs 0).ne_zero (hs 2).ne_zero hpos hsq
  rw [hsign]
  by_cases hc : c=1 <;> simp [signWeight,hc,mul_comm]

/-- A support zero, square-product parity, or proved local character row. -/
inductive PrimeConstraint (s : ℕ) where
  | zero (c : Fin 3) (j : Fin s)
  | product (j : Fin s)
  | character (c : Fin 3) (j : Fin s) (weights : Fin 3 → ZMod 2)

def constraintRow {s : ℕ} (ps : Fin s → ℕ) :
    PrimeConstraint s → Fin (BitDimension s) → ZMod 2
  | .zero c j => selectorRow (rawIndex c j)
  | .product j => ∑ c : Fin 3, selectorRow (rawIndex c j)
  | .character c j w => characterRow ps c (ps j)+
      ∑ c' : Fin 3, w c' • selectorRow (rawIndex c' j)

def constraintValue {s : ℕ} (ps : Fin s → ℕ) (d : ECFullTriple) :
    PrimeConstraint s → ZMod 2
  | .zero c j => primeBit (ps j) (coefficient d c)
  | .product j => ∑ c : Fin 3, primeBit (ps j) (coefficient d c)
  | .character c j w => modularParity (ps j) (SplitTwistPrime.unitPart (ps j) (coefficient d c))+
      ∑ c' : Fin 3, w c'*primeBit (ps j) (coefficient d c')

theorem constraintRow_source {s : ℕ} (ps : Fin s → ℕ)
    (hinj : Function.Injective ps) (hprime : ∀ i, (ps i).Prime)
    (d : ECFullTriple) (k : ℕ) (hs : ∀ c, Squarefree (coefficient d c))
    (hdiv : ∀ c, (coefficient d c).natAbs∣(∏ i, ps i)^k)
    (hpos : 0<d.2.1) (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (q : PrimeConstraint s) :
    constraintRow ps q ⬝ᵥ bitVector ps d=constraintValue ps d q := by
  cases q with
  | zero c j => simp [constraintRow,constraintValue]
  | product j => simp [constraintRow,constraintValue,sum_dotProduct]
  | character c j w =>
    rw [constraintRow,add_dotProduct,
      characterRow_source ps hinj hprime d k hs hdiv hpos hsq]
    simp [constraintValue,sum_dotProduct,smul_dotProduct,smul_eq_mul]

/-- The character of a product selected by divisibility bits. -/
theorem modularParity_selected_product (p : ℕ) [Fact p.Prime]
    (d : ECFullTriple) (f : Fin 3 → ℤ) (hf : ∀ c, (f c : ZMod p)≠0) :
    modularParity p (∏ c, if (p : ℤ)∣coefficient d c then f c else 1)=
      ∑ c, primeBit p (coefficient d c)*modularParity p (f c) := by
  have h := modularParity_product_powers p f (fun c => primeBit p (coefficient d c)) hf
  have he (c : Fin 3) : (f c)^(primeBit p (coefficient d c)).val=
      if (p : ℤ)∣coefficient d c then f c else 1 := by
    rw [primeBit_val]
    split_ifs <;> simp
  simpa only [he] using h

/-- A square condition on a unit coefficient with selected constant
factors is exactly the corresponding weighted character constraint. -/
theorem character_constraint_of_selected_square {s : ℕ} (ps : Fin s → ℕ)
    (d : ECFullTriple) (c : Fin 3) (j : Fin s) [Fact (ps j).Prime]
    (hs : Squarefree (coefficient d c)) (f : Fin 3 → ℤ)
    (hf : ∀ c', (f c' : ZMod (ps j))≠0)
    (hq : IsSquare ((SplitTwistPrime.unitPart (ps j) (coefficient d c)*
      (∏ c', if (ps j : ℤ)∣coefficient d c' then f c' else 1) : ℤ) : ZMod (ps j))) :
    constraintValue ps d (.character c j (fun c' => modularParity (ps j) (f c')))=0 := by
  have hU := SplitTwistPrime.unitPart_cast_ne_zero (p:=ps j) (coefficient d c) hs
  have hP : (((∏ c', if (ps j : ℤ)∣coefficient d c' then f c' else 1 : ℤ)) : ZMod (ps j))≠0 := by
    push_cast
    apply Finset.prod_ne_zero_iff.mpr
    intro c' _
    split_ifs <;> simp_all
  have h := (modularParity_eq_zero_iff (ps j) _).mpr hq
  rw [modularParity_mul _ _ _ hU hP,modularParity_selected_product _ d f hf] at h
  simpa only [constraintValue,mul_comm] using h


end
end Z2Z4Rank6.TwistSelmer
