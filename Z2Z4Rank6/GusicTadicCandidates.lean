module

public import Z2Z4Rank6.GusicTadicSquareClasses
public import Z2Z4Rank6.GusicTadicFactorization

@[expose] public section

/-!
# Polynomial candidate tests for the specialization criterion

Evaluation of the squarefree-factor candidate pools in Propositions 2.3 and
5.2 of Manvir Jaswal, DOI 10.5281/zenodo.23437117. Each candidate is a product of integer
polynomials with exponents zero or
one. Divisor representability is proved separately in the factorization and
criterion modules.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial
open scoped BigOperators
noncomputable section

local notation "T" => (Polynomial.X : ℤ[X])

def evalAt (m : ℚ) : ℤ[X] →+* ℚ := Polynomial.eval₂RingHom (Int.castRingHom ℚ) m

theorem map_baseFactors {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : R) (i : Fin 11) :
    f (baseFactors m i)=baseFactors (f m) i := by
  fin_cases i <;> simp [baseFactors, map_ofNat]

private theorem eval_bit_product {n : ℕ} (m : ℚ) (f : Fin n → ℤ[X]) (v : Fin n → ℚ)
    (he : ∀ i, evalAt m (f i)=v i) (b : Fin n → Fin 2) :
    evalAt m (∏ i, f i^(b i).val)=∏ i, v i^(b i).val := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, he]

/-- The integer-polynomial factors for this printed specialization. -/
def base14Polynomials : Fin 15 → ℤ[X] :=
  ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, -1, 2, 5, 7]

theorem base14_eval_polynomials (i : Fin 15) :
    evalAt (14/3) (base14Polynomials i)=base14Values i := by
  fin_cases i <;> simp [base14Polynomials, base14Values, map_baseFactors, evalAt, map_ofNat]

/-- Every square binary candidate product has the zero exponent vector. -/
theorem base14_candidate_test (b : Fin 15 → Fin 2)
    (h : IsSquare (evalAt (14/3) (∏ i, base14Polynomials i^(b i).val))) : b=0 := by
  rw [eval_bit_product _ _ _ base14_eval_polynomials] at h
  exact base14_squareclass_independent b h

/-- In particular, every nonempty candidate product has nonsquare value. -/
theorem base14_candidate_not_square (b : Fin 15 → Fin 2) (hb : b ≠ 0) :
    ¬IsSquare (evalAt (14/3) (∏ i, base14Polynomials i^(b i).val)) :=
  fun hs => hb (base14_candidate_test b hs)

/-- A nonconstant polynomial represented by the printed binary factor pool
has nonsquare specialization. -/
theorem base14_nonconstant_candidate (g : ℤ[X]) (b : Fin 15 → Fin 2)
    (hg : g=∏ i, base14Polynomials i^(b i).val) (hn : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (14/3) g) := by
  intro hs
  rw [hg] at hs
  have hb := base14_candidate_test b hs
  have hg1 : g=1 := by simpa only [hb, Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one

/-- The integer-polynomial factors for this printed specialization. -/
def twist14Polynomials : Fin 16 → ℤ[X] :=
  ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, 3*T^2+242, -1, 2, 5, 7]

theorem twist14_eval_polynomials (i : Fin 16) :
    evalAt (14/3) (twist14Polynomials i)=twist14Values i := by
  fin_cases i <;> simp [twist14Polynomials, twist14Values, map_baseFactors, evalAt, map_ofNat]

/-- Every square binary candidate product has the zero exponent vector. -/
theorem twist14_candidate_test (b : Fin 16 → Fin 2)
    (h : IsSquare (evalAt (14/3) (∏ i, twist14Polynomials i^(b i).val))) : b=0 := by
  rw [eval_bit_product _ _ _ twist14_eval_polynomials] at h
  exact twist14_squareclass_independent b h

/-- In particular, every nonempty candidate product has nonsquare value. -/
theorem twist14_candidate_not_square (b : Fin 16 → Fin 2) (hb : b ≠ 0) :
    ¬IsSquare (evalAt (14/3) (∏ i, twist14Polynomials i^(b i).val)) :=
  fun hs => hb (twist14_candidate_test b hs)

/-- A nonconstant polynomial represented by the printed binary factor pool
has nonsquare specialization. -/
theorem twist14_nonconstant_candidate (g : ℤ[X]) (b : Fin 16 → Fin 2)
    (hg : g=∏ i, twist14Polynomials i^(b i).val) (hn : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (14/3) g) := by
  intro hs
  rw [hg] at hs
  have hb := twist14_candidate_test b hs
  have hg1 : g=1 := by simpa only [hb, Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one

/-- The integer-polynomial factors for this printed specialization. -/
def twist50Polynomials : Fin 16 → ℤ[X] :=
  ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, 2*T^2+243, -1, 2, 5, 7]

theorem twist50_eval_polynomials (i : Fin 16) :
    evalAt (50/3) (twist50Polynomials i)=twist50Values i := by
  fin_cases i <;> simp [twist50Polynomials, twist50Values, map_baseFactors, evalAt, map_ofNat]

/-- Every square binary candidate product has the zero exponent vector. -/
theorem twist50_candidate_test (b : Fin 16 → Fin 2)
    (h : IsSquare (evalAt (50/3) (∏ i, twist50Polynomials i^(b i).val))) : b=0 := by
  rw [eval_bit_product _ _ _ twist50_eval_polynomials] at h
  exact twist50_squareclass_independent b h

/-- In particular, every nonempty candidate product has nonsquare value. -/
theorem twist50_candidate_not_square (b : Fin 16 → Fin 2) (hb : b ≠ 0) :
    ¬IsSquare (evalAt (50/3) (∏ i, twist50Polynomials i^(b i).val)) :=
  fun hs => hb (twist50_candidate_test b hs)

/-- A nonconstant polynomial represented by the printed binary factor pool
has nonsquare specialization. -/
theorem twist50_nonconstant_candidate (g : ℤ[X]) (b : Fin 16 → Fin 2)
    (hg : g=∏ i, twist50Polynomials i^(b i).val) (hn : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (50/3) g) := by
  intro hs
  rw [hg] at hs
  have hb := twist50_candidate_test b hs
  have hg1 : g=1 := by simpa only [hb, Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one

/-- The integer-polynomial factors for this printed specialization. -/
def product50Polynomials : Fin 17 → ℤ[X] :=
  ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, 2*T^2+243, 3*T^2+242, -1, 2, 5, 7]

theorem product50_eval_polynomials (i : Fin 17) :
    evalAt (50/3) (product50Polynomials i)=product50Values i := by
  fin_cases i <;> simp [product50Polynomials, product50Values, map_baseFactors, evalAt, map_ofNat]

/-- Every square binary candidate product has the zero exponent vector. -/
theorem product50_candidate_test (b : Fin 17 → Fin 2)
    (h : IsSquare (evalAt (50/3) (∏ i, product50Polynomials i^(b i).val))) : b=0 := by
  rw [eval_bit_product _ _ _ product50_eval_polynomials] at h
  exact product50_squareclass_independent b h

/-- In particular, every nonempty candidate product has nonsquare value. -/
theorem product50_candidate_not_square (b : Fin 17 → Fin 2) (hb : b ≠ 0) :
    ¬IsSquare (evalAt (50/3) (∏ i, product50Polynomials i^(b i).val)) :=
  fun hs => hb (product50_candidate_test b hs)

/-- A nonconstant polynomial represented by the printed binary factor pool
has nonsquare specialization. -/
theorem product50_nonconstant_candidate (g : ℤ[X]) (b : Fin 17 → Fin 2)
    (hg : g=∏ i, product50Polynomials i^(b i).val) (hn : g.natDegree ≠ 0) :
    ¬IsSquare (evalAt (50/3) g) := by
  intro hs
  rw [hg] at hs
  have hb := product50_candidate_test b hs
  have hg1 : g=1 := by simpa only [hb, Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one

end

end Z2Z4Rank6.GusicTadic
