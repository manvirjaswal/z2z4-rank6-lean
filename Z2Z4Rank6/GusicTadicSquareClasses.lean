import Z2Z4Rank6.GusicTadicData
import Z2Z4Rank6.TwoDescent
import Mathlib.Algebra.BigOperators.Fin

/-!
# The specialization squareclass tests

The unique-prime elimination in Propositions 2.3 and 5.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. Every witness is the parity of a
`padicValRat` on the rational factor value. The sign class is eliminated
by the fact that a negative rational number cannot be a square.
-/

namespace Z2Z4Rank6.GusicTadic

open scoped BigOperators

noncomputable section

private theorem squareClass_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, f i ≠ 0) :
    squareClass (∏ i ∈ s, f i)=∑ i ∈ s, squareClass (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [squareClass_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      squareClass_mul _ _ (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem squareClass_bit_product {n : ℕ} (f : Fin n → ℚ) (hf : ∀ i, f i ≠ 0)
    (b : Fin n → Fin 2) :
    squareClass (∏ i, f i^(b i).val)=∑ i, (b i).val • squareClass (f i) := by
  rw [squareClass_prod Finset.univ _ (fun i _ => pow_ne_zero _ (hf i))]
  apply Finset.sum_congr rfl
  intro i _
  exact squareClass_pow _ _ (hf i)

private theorem bit_cast_zero {b : Fin 2} (h : (b.val : ZMod 2)=0) : b=0 := by
  fin_cases b
  · rfl
  · norm_num at h

/-- A lower triangular family of additive valuation witnesses detects every
binary coefficient. The proof eliminates coefficients in their witness order. -/
private theorem triangular_elimination {n : ℕ} (V : Fin n → RatSquareClassAdd)
    (L : Fin n → RatSquareClassAdd →+ ZMod 2)
    (hdiag : ∀ i, L i (V i)=1)
    (htri : ∀ i j, i<j → L i (V j)=0)
    (b : Fin n → Fin 2) (h : ∀ i, ∑ j, (b j).val • L i (V j)=0) : b=0 := by
  have hstep : ∀ k : ℕ, ∀ i : Fin n, i.val<k → (b i).val=0 := by
    intro k
    induction k with
    | zero => intro i hi; omega
    | succ k ih =>
      intro i hi
      by_cases hik : i.val<k
      · exact ih i hik
      · have hieq : i.val=k := by omega
        have he := h i
        rw [Finset.sum_eq_single i] at he
        · have hbit : b i=0 := by
            apply bit_cast_zero
            simpa only [hdiag, nsmul_eq_mul, mul_one] using he
          simp [hbit]
        · intro j _ hji
          by_cases hj : j.val<k
          · rw [ih j hj, zero_nsmul]
          · have hij : i<j := by
              apply Fin.mk_lt_mk.mpr
              have hjne : j.val ≠ i.val := by intro hh; exact hji (Fin.ext hh)
              omega
            rw [htri i j hij, nsmul_zero]
        · simp
  funext i
  exact Fin.ext (hstep n i i.isLt)

private theorem bit_minus_one {b : Fin 2} (h : IsSquare ((-1 : ℚ)^b.val)) : b=0 := by
  fin_cases b
  · rfl
  · norm_num at h

/-- A triangular table of prime valuations, followed by the sign class,
proves that no nonempty product of the displayed squareclasses is a square. -/
theorem square_product_bits_zero {n : ℕ} (values : Fin (n+1) → ℚ)
    (hvalues : ∀ i, values i ≠ 0) (hsign : values (Fin.last n)= -1)
    (primes : Fin n → ℕ) (hprimes : ∀ i, (primes i).Prime)
    (hdiag : ∀ i, (padicValRat (primes i) (values i.castSucc) : ZMod 2)=1)
    (htri : ∀ i j, i<j → (padicValRat (primes i) (values j.castSucc) : ZMod 2)=0)
    (b : Fin (n+1) → Fin 2) (hsquare : IsSquare (∏ i, values i^(b i).val)) : b=0 := by
  let L : Fin n → RatSquareClassAdd →+ ZMod 2 := fun i => by
    letI : Fact (primes i).Prime := ⟨hprimes i⟩
    exact squareClassValuation (primes i)
  have hL (i : Fin n) (j : Fin (n+1)) :
      L i (squareClass (values j))=(padicValRat (primes i) (values j) : ZMod 2) := by
    let : Fact (primes i).Prime := ⟨hprimes i⟩
    exact squareClassValuation_apply _ _ (hvalues j)
  have hrel : ∑ i, (b i).val • squareClass (values i)=0 := by
    rw [← squareClass_bit_product values hvalues]
    exact squareClass_eq_zero_of_isSquare hsquare
  have hbits : (fun i : Fin n => b i.castSucc)=0 := by
    apply triangular_elimination (fun i => squareClass (values i.castSucc)) L
      (by intro i; rw [hL]; exact hdiag i)
      (by intro i j hij; rw [hL]; exact htri i j hij)
    intro i
    have he := congrArg (L i) hrel
    simp only [map_sum, map_add, map_nsmul, map_zero, Fin.sum_univ_castSucc] at he
    rw [hL i (Fin.last n), hsign] at he
    simpa only [padicValRat.neg, padicValRat.one, Int.cast_zero, nsmul_zero, add_zero] using he
  have hprod : (∏ i, values i^(b i).val)=(-1 : ℚ)^(b (Fin.last n)).val := by
    rw [Fin.prod_univ_castSucc]
    have hb (i : Fin n) : b i.castSucc=0 := congrFun hbits i
    simp only [hb, Fin.val_zero, pow_zero, Finset.prod_const_one, one_mul, hsign]
  rw [hprod] at hsquare
  have hlast := bit_minus_one hsquare
  funext j
  change b j=0
  by_cases hj : j.val<n
  · let i : Fin n := ⟨j.val,hj⟩
    have he : j=i.castSucc := Fin.ext rfl
    rw [he]
    exact congrFun hbits i
  · have he : j=Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he]
    exact hlast

private theorem base14_values_nonzero : ∀ i, base14OrderedValues i ≠ 0 := by decide +kernel

private theorem base14_witnesses_prime : ∀ i, (base14Witnesses i).Prime := by decide +kernel

private theorem base14_diagonal :
    ∀ i : Fin 14, (padicValRat (base14Witnesses i) (base14OrderedValues i.castSucc) : ZMod 2)=1 := by
  decide +kernel

private theorem base14_triangular :
    ∀ i j : Fin 14, i<j →
      (padicValRat (base14Witnesses i) (base14OrderedValues j.castSucc) : ZMod 2)=0 := by
  decide +kernel

/-- The eleven factor values at 14/3 and the four constant classes are independent,
in the unique-prime elimination order. -/
theorem base14_ordered_independent (b : Fin 15 → Fin 2)
    (h : IsSquare (∏ i, base14OrderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero base14OrderedValues base14_values_nonzero rfl base14Witnesses
    base14_witnesses_prime base14_diagonal base14_triangular b h

/-- Reindexing by an explicit equivalence preserves the squareclass test. -/
private theorem independent_of_permutation {n : ℕ} (values : Fin n → ℚ)
    (e : Equiv.Perm (Fin n))
    (hind : ∀ b : Fin n → Fin 2, IsSquare (∏ i, values (e i)^(b i).val) → b=0)
    (b : Fin n → Fin 2) (h : IsSquare (∏ i, values i^(b i).val)) : b=0 := by
  have he : IsSquare (∏ i, values (e i)^(b (e i)).val) := by
    rw [Equiv.prod_comp e (fun i => values i^(b i).val)]
    exact h
  have hb := hind (fun i => b (e i)) he
  funext i
  have hi := congrFun hb (e.symm i)
  simpa only [e.apply_symm_apply, Pi.zero_apply] using hi

/-- Proposition 2.3: the eleven printed factor values at 14/3, followed by
-1,2,5,7, have independent classes in the rational squareclass group. -/
theorem base14_squareclass_independent (b : Fin 15 → Fin 2)
    (h : IsSquare (∏ i, base14Values i^(b i).val)) : b=0 :=
  independent_of_permutation base14Values base14Order base14_ordered_independent b h

private theorem twist14_values_nonzero : ∀ i, twist14OrderedValues i ≠ 0 := by decide +kernel

private theorem twist14_witnesses_prime : ∀ i, (twist14Witnesses i).Prime := by decide +kernel

private theorem twist14_diagonal :
    ∀ i : Fin 15, (padicValRat (twist14Witnesses i) (twist14OrderedValues i.castSucc) : ZMod 2)=1 := by
  decide +kernel

private theorem twist14_triangular :
    ∀ i j : Fin 15, i<j →
      (padicValRat (twist14Witnesses i) (twist14OrderedValues j.castSucc) : ZMod 2)=0 := by
  decide +kernel

/-- The printed specialization classes are independent in their unique-prime order. -/
theorem twist14_ordered_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, twist14OrderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero twist14OrderedValues twist14_values_nonzero rfl twist14Witnesses
    twist14_witnesses_prime twist14_diagonal twist14_triangular b h

/-- Proposition 5.2: the printed factors at the indicated specialization, with
the four content/sign classes -1,2,5,7, have no nonempty square product. -/
theorem twist14_squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, twist14Values i^(b i).val)) : b=0 :=
  independent_of_permutation twist14Values twist14Order twist14_ordered_independent b h

private theorem twist50_values_nonzero : ∀ i, twist50OrderedValues i ≠ 0 := by decide +kernel

private theorem twist50_witnesses_prime : ∀ i, (twist50Witnesses i).Prime := by
  intro i
  fin_cases i <;> norm_num [twist50Witnesses]

private theorem twist50_diagonal :
    ∀ i : Fin 15, (padicValRat (twist50Witnesses i) (twist50OrderedValues i.castSucc) : ZMod 2)=1 := by
  decide +kernel

private theorem twist50_triangular :
    ∀ i j : Fin 15, i<j →
      (padicValRat (twist50Witnesses i) (twist50OrderedValues j.castSucc) : ZMod 2)=0 := by
  decide +kernel

/-- The printed specialization classes are independent in their unique-prime order. -/
theorem twist50_ordered_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, twist50OrderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero twist50OrderedValues twist50_values_nonzero rfl twist50Witnesses
    twist50_witnesses_prime twist50_diagonal twist50_triangular b h

/-- Proposition 5.2: the printed factors at the indicated specialization, with
the four content/sign classes -1,2,5,7, have no nonempty square product. -/
theorem twist50_squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, twist50Values i^(b i).val)) : b=0 :=
  independent_of_permutation twist50Values twist50Order twist50_ordered_independent b h

private theorem product50_values_nonzero : ∀ i, product50OrderedValues i ≠ 0 := by decide +kernel

private theorem product50_witnesses_prime : ∀ i, (product50Witnesses i).Prime := by
  intro i
  fin_cases i <;> norm_num [product50Witnesses]

private theorem product50_diagonal :
    ∀ i : Fin 16, (padicValRat (product50Witnesses i) (product50OrderedValues i.castSucc) : ZMod 2)=1 := by
  decide +kernel

private theorem product50_triangular :
    ∀ i j : Fin 16, i<j →
      (padicValRat (product50Witnesses i) (product50OrderedValues j.castSucc) : ZMod 2)=0 := by
  decide +kernel

/-- The printed specialization classes are independent in their unique-prime order. -/
theorem product50_ordered_independent (b : Fin 17 → Fin 2)
    (h : IsSquare (∏ i, product50OrderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero product50OrderedValues product50_values_nonzero rfl product50Witnesses
    product50_witnesses_prime product50_diagonal product50_triangular b h

/-- Proposition 5.2: the printed factors at the indicated specialization, with
the four content/sign classes -1,2,5,7, have no nonempty square product. -/
theorem product50_squareclass_independent (b : Fin 17 → Fin 2)
    (h : IsSquare (∏ i, product50Values i^(b i).val)) : b=0 :=
  independent_of_permutation product50Values product50Order product50_ordered_independent b h

end

end Z2Z4Rank6.GusicTadic
