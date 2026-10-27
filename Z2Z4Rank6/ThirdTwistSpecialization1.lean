import Z2Z4Rank6.ThirdTwistData
import Z2Z4Rank6.GusicTadicDivisors
import Z2Z4Rank6.GusicTadicRadicals
import Z2Z4Rank6.GusicTadicSquareClasses

/-! The printed third-twist factor table and complete squarefree divisor test,
Jaswal, paragraph after Proposition 7.2, DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ThirdTwist.Specialization1
open Polynomial GusicTadic
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
local notation "T" => (Polynomial.X : ℤ[X])
def values : Fin 18 → ℚ := ![baseFactors (parameter 1) 0, baseFactors (parameter 1) 1, baseFactors (parameter 1) 2, baseFactors (parameter 1) 3, baseFactors (parameter 1) 4, baseFactors (parameter 1) 5, baseFactors (parameter 1) 6, baseFactors (parameter 1) 7, baseFactors (parameter 1) 8, baseFactors (parameter 1) 9, baseFactors (parameter 1) 10, q3 (parameter 1), 3*(parameter 1)^2+242, 2*(parameter 1)^2+243, -1, 2, 5, 7]
def representatives : Fin 18 → ℤ := ![-1065, -165, -273, -93, 717, -183, -3, -255, -174, 2473, 481993, 13861, 12270, 8915, -1, 2, 5, 7]
def squareFactors : Fin 18 → ℚ := ![1/3, 1/3, 1/3, 1/3, 1/3, 1/3, 5/3, 1/3, 1/3, 1/3, 5/9, 1/3, 1/3, 1/3, 1, 1, 1, 1]
theorem representative_identities (i : Fin 18) :
    values i=(representatives i : ℚ)*(squareFactors i)^2 := by
  fin_cases i <;> norm_num [values,representatives,squareFactors,baseFactors,parameter,q3]
theorem representatives_squarefree (i : Fin 18) : Squarefree (representatives i).natAbs := by
  fin_cases i
  · change Squarefree 1065
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 355)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 5 71)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 71 by norm_num).squarefree⟩⟩
  · change Squarefree 165
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 55)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 5 11)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 11 by norm_num).squarefree⟩⟩
  · change Squarefree 273
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 91)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 7 13)).2 ⟨(show Nat.Prime 7 by norm_num).squarefree,(show Nat.Prime 13 by norm_num).squarefree⟩⟩
  · change Squarefree 93
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 31)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 31 by norm_num).squarefree⟩
  · change Squarefree 717
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 239)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 239 by norm_num).squarefree⟩
  · change Squarefree 183
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 61)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 61 by norm_num).squarefree⟩
  · change Squarefree 3
    exact (show Nat.Prime 3 by norm_num).squarefree
  · change Squarefree 255
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 3 85)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 5 17)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 17 by norm_num).squarefree⟩⟩
  · change Squarefree 174
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 87)).2 ⟨(show Nat.Prime 2 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 3 29)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(show Nat.Prime 29 by norm_num).squarefree⟩⟩
  · change Squarefree 2473
    exact (show Nat.Prime 2473 by norm_num).squarefree
  · change Squarefree 481993
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 97 4969)).2 ⟨(show Nat.Prime 97 by norm_num).squarefree,(show Nat.Prime 4969 by norm_num).squarefree⟩
  · change Squarefree 13861
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 83 167)).2 ⟨(show Nat.Prime 83 by norm_num).squarefree,(show Nat.Prime 167 by norm_num).squarefree⟩
  · change Squarefree 12270
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 6135)).2 ⟨(show Nat.Prime 2 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 3 2045)).2 ⟨(show Nat.Prime 3 by norm_num).squarefree,(Nat.squarefree_mul (by decide : Nat.Coprime 5 409)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 409 by norm_num).squarefree⟩⟩⟩
  · change Squarefree 8915
    exact (Nat.squarefree_mul (by decide : Nat.Coprime 5 1783)).2 ⟨(show Nat.Prime 5 by norm_num).squarefree,(show Nat.Prime 1783 by norm_num).squarefree⟩
  · change Squarefree 1
    exact squarefree_one
  · change Squarefree 2
    exact (show Nat.Prime 2 by norm_num).squarefree
  · change Squarefree 5
    exact (show Nat.Prime 5 by norm_num).squarefree
  · change Squarefree 7
    exact (show Nat.Prime 7 by norm_num).squarefree
def order : Equiv.Perm (Fin 18) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 6, 13, 15, 16, 17, 14] : Fin 18 → Fin 18) (by decide +kernel)
def orderedValues (i : Fin 18) : ℚ := values (order i)
def witnesses : Fin 17 → ℕ := ![71, 11, 13, 31, 239, 61, 17, 29, 2473, 97, 83, 409, 3, 1783, 2, 5, 7]
private theorem values_nonzero : ∀i,orderedValues i≠0 := by decide +kernel
private theorem witnesses_prime (i : Fin 17) : (witnesses i).Prime := by
  fin_cases i <;> norm_num [witnesses]
private theorem diagonal : ∀i : Fin 17,
    (padicValRat (witnesses i) (orderedValues i.castSucc) : ZMod 2)=1 := by decide +kernel
private theorem triangular : ∀i j : Fin 17,i<j →
    (padicValRat (witnesses i) (orderedValues j.castSucc) : ZMod 2)=0 := by decide +kernel
theorem ordered_squareclass_independent (b : Fin 18 → Fin 2)
    (h : IsSquare (∏i,orderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero orderedValues values_nonzero rfl witnesses
    witnesses_prime diagonal triangular b h
theorem squareclass_independent (b : Fin 18 → Fin 2)
    (h : IsSquare (∏i,values i^(b i).val)) : b=0 := by
  have he : IsSquare (∏i,orderedValues i^(b (order i)).val) := by
    unfold orderedValues
    rw [Equiv.prod_comp order (fun i => values i^(b i).val)]
    exact h
  have hb := ordered_squareclass_independent (fun i => b (order i)) he
  funext i
  have hi := congrFun hb (order.symm i)
  simpa only [order.apply_symm_apply,Pi.zero_apply] using hi
def polynomials : Fin 18 → ℤ[X] := ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, q3Poly, 3*T^2+242, 2*T^2+243, -1, 2, 5, 7]
theorem eval_polynomials (i : Fin 18) : evalAt (parameter 1) (polynomials i)=values i := by
  fin_cases i <;> norm_num [polynomials,values,evalAt,baseFactors,q3Poly,q3,parameter]
theorem candidate_test (b : Fin 18 → Fin 2)
    (h : IsSquare (evalAt (parameter 1) (∏i,polynomials i^(b i).val))) : b=0 := by
  have he : evalAt (parameter 1) (∏i,polynomials i^(b i).val)=∏i,values i^(b i).val := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow,eval_polynomials]
  rw [he] at h
  exact squareclass_independent b h
theorem nonconstant_candidate (g : ℤ[X]) (b : Fin 18 → Fin 2)
    (hg : g=∏i,polynomials i^(b i).val) (hn : g.natDegree≠0) :
    ¬IsSquare (evalAt (parameter 1) g) := by
  intro hs
  rw [hg] at hs
  have hb := candidate_test b hs
  have hg1 : g=1 := by
    simpa only [hb,Pi.zero_apply,Fin.val_zero,pow_zero,Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one
def radical : ℤ[X] := baseRadical*q3Poly*(3*T^2+242)*(2*T^2+243)
theorem pool_product : (∏i : Fin 17,polynomials (order i.castSucc))=radical := by
  norm_num [Fin.prod_univ_succ,polynomials,order,baseFactors,radical,baseRadical,
    linearA,linearB,quadraticFactor,quarticFactor]
  ring
private theorem ordered_irreducible (i : Fin 17) :
    Irreducible (polynomials (order i.castSucc)) := by
  fin_cases i
  · simpa [polynomials,order] using baseFactors_irreducible 0
  · simpa [polynomials,order] using baseFactors_irreducible 1
  · simpa [polynomials,order] using baseFactors_irreducible 2
  · simpa [polynomials,order] using baseFactors_irreducible 3
  · simpa [polynomials,order] using baseFactors_irreducible 4
  · simpa [polynomials,order] using baseFactors_irreducible 5
  · simpa [polynomials,order] using baseFactors_irreducible 7
  · simpa [polynomials,order] using baseFactors_irreducible 8
  · simpa [polynomials,order] using baseFactors_irreducible 9
  · simpa [polynomials,order] using baseFactors_irreducible 10
  · simpa [polynomials,order] using q3Poly_irreducible
  · simpa [polynomials,order] using q1Core_irreducible
  · simpa [polynomials,order] using baseFactors_irreducible 6
  · simpa [polynomials,order] using q2Core_irreducible
  · simpa [polynomials,order] using contentPrime_irreducible 2 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 5 (by decide)
  · simpa [polynomials,order] using contentPrime_irreducible 7 (by decide)
theorem twist_dvd_radical : twistPolynomial 1∣radical := by
  refine ⟨14*linearA*linearB*T*quadraticFactor*quarticFactor*(2*T^2+243),?_⟩
  unfold twistPolynomial radical q1Poly q2Poly q12Poly q1 q2 q12 baseRadical
  dsimp
  ring
theorem base_dvd_radical : baseRadical∣radical := by
  refine ⟨q3Poly*(3*T^2+242)*(2*T^2+243),?_⟩
  unfold radical
  ring
theorem products_dvd_radical (i : Fin 3) :
    (twistPolynomial 1)^2*rootDifferenceProducts i∣radical^6 := by
  have hq2 := pow_dvd_pow_of_dvd twist_dvd_radical 2
  have hp4 := (rootDifferenceProducts_dvd_radical i).trans
    (pow_dvd_pow_of_dvd base_dvd_radical 4)
  simpa only [←pow_add,show 2+4=6 by decide] using mul_dvd_mul hq2 hp4
theorem divisor_representation (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣(twistPolynomial 1)^2*rootDifferenceProducts i) :
    ∃b : Fin 18 → Fin 2,g=∏j,polynomials j^(b j).val := by
  have hR : g∣radical := (hsq.dvd_pow_iff_dvd (by decide : 6≠0)).mp
    (hdiv.trans (products_dvd_radical i))
  rw [←pool_product] at hR
  apply binary_representation_unpermute polynomials order g
  exact divisor_binary_representation (fun j => polynomials (order j))
    ordered_irreducible rfl g hR
theorem divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣(twistPolynomial 1)^2*rootDifferenceProducts i)
    (hn : g.natDegree≠0) : ¬IsSquare (evalAt (parameter 1) g) := by
  obtain ⟨b,hb⟩ := divisor_representation i g hsq hdiv
  exact nonconstant_candidate g b hb hn
theorem twist2_dvd_radical : twistPolynomial 2∣radical := by
  refine ⟨14*linearA*linearB*T*quadraticFactor*quarticFactor*(3*T^2+242),?_⟩
  unfold twistPolynomial radical q1Poly q2Poly q12Poly q1 q2 q12 baseRadical
  dsimp
  ring
theorem divisor_test2 (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣(twistPolynomial 2)^2*rootDifferenceProducts i)
    (hn : g.natDegree≠0) : ¬IsSquare (evalAt (parameter 2) g) := by
  have hp : (twistPolynomial 2)^2*rootDifferenceProducts i∣radical^6 := by
    have hq2 := pow_dvd_pow_of_dvd twist2_dvd_radical 2
    have hp4 := (rootDifferenceProducts_dvd_radical i).trans
      (pow_dvd_pow_of_dvd base_dvd_radical 4)
    simpa only [←pow_add,show 2+4=6 by decide] using mul_dvd_mul hq2 hp4
  have hR : g∣radical := (hsq.dvd_pow_iff_dvd (by decide : 6≠0)).mp (hdiv.trans hp)
  rw [←pool_product] at hR
  obtain ⟨b,hb⟩ := binary_representation_unpermute polynomials order g
    (divisor_binary_representation (fun j => polynomials (order j)) ordered_irreducible rfl g hR)
  exact nonconstant_candidate g b hb hn

end
end Z2Z4Rank6.ThirdTwist.Specialization1
