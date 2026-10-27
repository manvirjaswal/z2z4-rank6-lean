import Z2Z4Rank6.GSpecializationPolynomials
import Z2Z4Rank6.GusicTadicSquareClasses
import Z2Z4Rank6.GusicTadicCandidates

/-!
# The twelve specialization factors at m=-80/3

The data come from the printed table in
Proposition 7.2(b) of Jaswal, DOI: 10.5281/zenodo.23437117.
Exact rational squares certify all printed representatives; prime
valuations and the sign detect every binary product.
-/

namespace Z2Z4Rank6.GSpecialization

open Polynomial GusicTadic
open scoped BigOperators
noncomputable section
local notation "T" => (Polynomial.X : ℤ[X])

def values : Fin 16 → ℚ := ![baseFactors parameter 0, baseFactors parameter 1, baseFactors parameter 2, baseFactors parameter 3, baseFactors parameter 4, baseFactors parameter 5, baseFactors parameter 6, baseFactors parameter 7, baseFactors parameter 8, baseFactors parameter 9, baseFactors parameter 10, 99*parameter^4-9998*parameter^2+970299, -1, 2, 5, 7]
def representatives : Fin 16 → ℤ := ![-1131, -231, -339, -159, 651, -249, -141, -321, -15, 5509, 849769, 8067459, -1, 2, 5, 7]
def squareFactors : Fin 16 → ℚ := ![(1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (4)/3, (1)/3, (7)/9, (7)/3, 1, 1, 1, 1]

theorem representative_identities (i : Fin 16) :
    values i=(representatives i : ℚ)*(squareFactors i)^2 := by
  fin_cases i <;> norm_num [values,representatives,squareFactors,baseFactors,
    parameter,GTwistSelmer.parameter]

theorem representatives_squarefree (i : Fin 16) : Squarefree (representatives i).natAbs := by
  fin_cases i <;> decide +kernel

def order : Equiv.Perm (Fin 16) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 8, 13, 14, 15, 12] : Fin 16 → Fin 16) (by decide +kernel)
def orderedValues (i : Fin 16) : ℚ := values (order i)
def witnesses : Fin 15 → ℕ := ![29, 11, 113, 53, 31, 83, 47, 107, 787, 593, 1291, 3, 2, 5, 7]

private theorem values_nonzero : ∀ i, orderedValues i ≠ 0 := by decide +kernel
private theorem witnesses_prime : ∀ i, (witnesses i).Prime := by decide +kernel
private theorem diagonal : ∀ i : Fin 15,
    (padicValRat (witnesses i) (orderedValues i.castSucc) : ZMod 2)=1 := by decide +kernel
private theorem triangular : ∀ i j : Fin 15, i<j →
    (padicValRat (witnesses i) (orderedValues j.castSucc) : ZMod 2)=0 := by decide +kernel

theorem ordered_squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, orderedValues i^(b i).val)) : b=0 :=
  square_product_bits_zero orderedValues values_nonzero rfl witnesses
    witnesses_prime diagonal triangular b h

theorem squareclass_independent (b : Fin 16 → Fin 2)
    (h : IsSquare (∏ i, values i^(b i).val)) : b=0 := by
  have he : IsSquare (∏ i, orderedValues i^(b (order i)).val) := by
    unfold orderedValues
    rw [Equiv.prod_comp order (fun i => values i^(b i).val)]
    exact h
  have hb := ordered_squareclass_independent (fun i => b (order i)) he
  funext i
  have hi := congrFun hb (order.symm i)
  simpa only [order.apply_symm_apply,Pi.zero_apply] using hi

def polynomials : Fin 16 → ℤ[X] := ![baseFactors T 0, baseFactors T 1, baseFactors T 2, baseFactors T 3, baseFactors T 4, baseFactors T 5, baseFactors T 6, baseFactors T 7, baseFactors T 8, baseFactors T 9, baseFactors T 10, hPoly, -1, 2, 5, 7]

theorem eval_polynomials (i : Fin 16) : evalAt parameter (polynomials i)=values i := by
  fin_cases i <;> norm_num [polynomials,values,evalAt,baseFactors,hPoly,
    GTwistSelmer.hPolynomial,parameter,GTwistSelmer.parameter]

theorem candidate_test (b : Fin 16 → Fin 2)
    (h : IsSquare (evalAt parameter (∏ i, polynomials i^(b i).val))) : b=0 := by
  have he : evalAt parameter (∏ i, polynomials i^(b i).val)=∏ i, values i^(b i).val := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [map_pow,eval_polynomials]
  rw [he] at h
  exact squareclass_independent b h

theorem nonconstant_candidate (g : ℤ[X]) (b : Fin 16 → Fin 2)
    (hg : g=∏ i, polynomials i^(b i).val) (hn : g.natDegree≠0) :
    ¬IsSquare (evalAt parameter g) := by
  intro hs
  rw [hg] at hs
  have hb := candidate_test b hs
  have hg1 : g=1 := by
    simpa only [hb,Pi.zero_apply,Fin.val_zero,pow_zero,Finset.prod_const_one] using hg
  rw [hg1] at hn
  exact hn Polynomial.natDegree_one

end
end Z2Z4Rank6.GSpecialization
