module

public import Z2Z4Rank6.ThirdTwistData
public import Z2Z4Rank6.GusicTadicDivisors
public import Z2Z4Rank6.GusicTadicRadicals
public import Z2Z4Rank6.GusicTadicSquareClasses

@[expose] public section

/-! The printed third-twist factor table and complete squarefree divisor test,
Jaswal, paragraph after Proposition 7.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Specialization0
open Polynomial GusicTadic
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
local notation "T" => (Polynomial.X : ℤ[X])
def values : Fin 16 → ℚ := ![baseFactors (parameter 0) 0, baseFactors (parameter 0) 1, baseFactors (parameter 0) 2, baseFactors (parameter 0) 3, baseFactors (parameter 0) 4, baseFactors (parameter 0) 5, baseFactors (parameter 0) 6, baseFactors (parameter 0) 7, baseFactors (parameter 0) 8, baseFactors (parameter 0) 9, baseFactors (parameter 0) 10, q3 (parameter 0), -1, 2, 5, 7]
def representatives : Fin 16 → ℤ := ![-57, 43, 31, 51, 141, 41, 53, 33, 42, 185, 346441, 789, -1, 2, 5, 7]
def squareFactors : Fin 16 → ℚ := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1]
theorem representative_identities (i : Fin 16) :
    values i=(representatives i : ℚ)*(squareFactors i)^2 := by
  fin_cases i <;> norm_num [values,representatives,squareFactors,baseFactors,parameter,q3]
theorem representatives_squarefree (i : Fin 16) : Squarefree (representatives i).natAbs := by
  fin_cases i
  · change Squarefree 57
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 19)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 19 by norm_num).squarefree⟩
  · change Squarefree 43
    exact (show Nat.Prime 43 by norm_num).squarefree
  · change Squarefree 31
    exact (show Nat.Prime 31 by norm_num).squarefree
  · change Squarefree 51
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 17)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 17 by norm_num).squarefree⟩
  · change Squarefree 141
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 47)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 47 by norm_num).squarefree⟩
  · change Squarefree 41
    exact (show Nat.Prime 41 by norm_num).squarefree
  · change Squarefree 53
    exact (show Nat.Prime 53 by norm_num).squarefree
  · change Squarefree 33
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 11)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 11 by norm_num).squarefree⟩
  · change Squarefree 42
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 21)).2 ⟨(show Nat.Prime 2 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 7 by norm_num).squarefree⟩⟩
  · change Squarefree 185
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 5 37)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 37 by norm_num).squarefree⟩
  · change Squarefree 346441
    exact (show Nat.Prime 346441 by norm_num).squarefree
  · change Squarefree 789
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 263)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 263 by norm_num).squarefree⟩
  · change Squarefree 1
    exact squarefree_one
  · change Squarefree 2
    exact (show Nat.Prime 2 by norm_num).squarefree
  · change Squarefree 5
    exact (show Nat.Prime 5 by norm_num).squarefree
  · change Squarefree 7
    exact (show Nat.Prime 7 by norm_num).squarefree
def order : Equiv.Perm (Fin 16) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 8, 13, 14, 15, 12] : Fin 16 → Fin 16) (by decide +kernel)
def orderedValues (i : Fin 16) : ℚ := values (order i)
def witnesses : Fin 15 → ℕ := ![19, 43, 31, 17, 47, 41, 53, 11, 37, 346441, 263, 3, 2, 5, 7]
private theorem values_nonzero : ∀i,orderedValues i≠0 := by decide +kernel
private theorem witnesses_prime (i : Fin 15) : (witnesses i).Prime := by
  fin_cases i <;> norm_num [witnesses]
private theorem diagonal : ∀i : Fin 15,
    (padicValRat (witnesses i) (orderedValues i.castSucc) : ZMod 2)=1 := by decide +kernel
private theorem triangular : ∀i j : Fin 15,i<j →
    (padicValRat (witnesses i) (orderedValues j.castSucc) : ZMod 2)=0 := by decide +kernel
theorem ordered_squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏i,orderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero orderedValues values_nonzero rfl witnesses
    witnesses_prime diagonal triangular b h
theorem squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏i,values i^(b i).val)) : b=0 := by
  have he : IsSquare (∏i,orderedValues i^(b (order i)).val) := by
    unfold orderedValues
    rw [Equiv.prod_comp order (fun i => values i^(b i).val)]
    exact h
  have hb := ordered_squareclass_independent (fun i => b (order i)) he
  funext i
  have hi := congrFun hb (order.symm i)
  simpa only [order.apply_symm_apply,Pi.zero_apply] using hi
def polynomials : Fin 16 → ℤ[X] := ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, q3Poly, -1, 2, 5, 7]
theorem eval_polynomials (i : Fin 16) : evalAt (parameter 0) (polynomials i)=values i := by
  fin_cases i <;> norm_num [polynomials,values,evalAt,baseFactors,q3Poly,q3,parameter]
theorem candidate_test (b : Fin 16 → Fin 2)
    (h : IsSquare (evalAt (parameter 0) (∏i,polynomials i^(b i).val))) : b=0 := by
  have he : evalAt (parameter 0) (∏i,polynomials i^(b i).val)=∏i,values i^(b i).val := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow,eval_polynomials]
  rw [he] at h
  exact squareclass_independent b h
theorem nonconstant_candidate (g : ℤ[X]) (b : Fin 16 → Fin 2)
    (hg : g=∏i,polynomials i^(b i).val) (hn : g.natDegree≠0) :
    ¬IsSquare (evalAt (parameter 0) g) := by
  intro hs
  rw [hg] at hs
  have hb := candidate_test b hs
  have hg1 : g=1 := by
    simpa only [hb,Pi.zero_apply,Fin.val_zero,pow_zero,Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one
def radical : ℤ[X] := baseRadical*q3Poly
theorem pool_product : (∏i : Fin 15,polynomials (order i.castSucc))=radical := by
  norm_num [Fin.prod_univ_succ,polynomials,order,baseFactors,radical,baseRadical,
    linearA,linearB,quadraticFactor,quarticFactor]
  ring
private theorem ordered_irreducible (i : Fin 15) :
    Irreducible (polynomials (order i.castSucc)) := by
  fin_cases i
  · simpa [polynomials,order] using baseFactors_irreducible 0
  · simpa [polynomials,order] using baseFactors_irreducible 1
  · simpa [polynomials,order] using baseFactors_irreducible 2
  · simpa [polynomials,order] using baseFactors_irreducible 3
  · simpa [polynomials,order] using baseFactors_irreducible 4
  · simpa [polynomials,order] using baseFactors_irreducible 5
  · simpa [polynomials,order] using baseFactors_irreducible 6
  · simpa [polynomials,order] using baseFactors_irreducible 7
  · simpa [polynomials,order] using baseFactors_irreducible 9
  · simpa [polynomials,order] using baseFactors_irreducible 10
  · simpa [polynomials,order] using q3Poly_irreducible
  · simpa [polynomials,order] using baseFactors_irreducible 8
  · simpa [polynomials,order] using contentPrime_irreducible 2 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 5 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 7 (by decide)
theorem twist_dvd_radical : twistPolynomial 0∣radical := by
  refine ⟨baseRadical,?_⟩
  unfold twistPolynomial radical q1Poly q2Poly q12Poly q1 q2 q12 baseRadical
  dsimp
  ring
theorem base_dvd_radical : baseRadical∣radical := by
  refine ⟨q3Poly,?_⟩
  unfold radical
  ring
theorem products_dvd_radical (i : Fin 3) :
    (twistPolynomial 0)^2*rootDifferenceProducts i∣radical^6 := by
  have hq2 := pow_dvd_pow_of_dvd twist_dvd_radical 2
  have hp4 := (rootDifferenceProducts_dvd_radical i).trans
    (pow_dvd_pow_of_dvd base_dvd_radical 4)
  simpa only [←pow_add,show 2+4=6 by decide] using mul_dvd_mul hq2 hp4
theorem divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣(twistPolynomial 0)^2*rootDifferenceProducts i) :
    ∃b : Fin 16 → Fin 2,g=∏j,polynomials j^(b j).val := by
  have hR : g∣radical := (hsq.dvd_pow_iff_dvd (by decide : 6≠0)).mp
    (hdiv.trans (products_dvd_radical i))
  rw [←pool_product] at hR
  apply binary_representation_unpermute polynomials order g
  exact divisor_binary_representation (fun j => polynomials (order j))
    ordered_irreducible rfl g hR
theorem divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣(twistPolynomial 0)^2*rootDifferenceProducts i)
    (hn : g.natDegree≠0) : ¬IsSquare (evalAt (parameter 0) g) := by
  obtain ⟨b,hb⟩ := divisor_representation i g hsq hdiv
  exact nonconstant_candidate g b hb hn

end
end Z2Z4Rank6.ThirdTwist.Specialization0
