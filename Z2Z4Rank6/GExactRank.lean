module

public import Z2Z4Rank6.GQuadraticRanks
public import Z2Z4Rank6.GFunctionFieldSpecialization
public import Z2Z4Rank6.RankThreeExact
public import Z2Z4Rank6.GSpecialization
public import Z2Z4Rank6.RankFiniteIndex
public import Z2Z4Rank6.GTwistSelmerExactRank

@[expose] public section

/-!
# Rank bounds for the Q(G) family

Proposition 7.2(b) of Jaswal, DOI: 10.5281/zenodo.23437117. The
five-point independence and proved quadratic decomposition give the h-twist
rank lower bound.
-/

namespace Z2Z4Rank6.GExactRank

noncomputable section

open GFunctionField.QuadraticCharacters

private theorem nat_le_of_nat_add_le (n m : ℕ) (r : Cardinal)
    (h : (n+m : Cardinal) ≤ n+r) : (m : Cardinal) ≤ r := by
  by_contra hn
  have hf : r < Cardinal.aleph0 := lt_trans (lt_of_not_ge hn) (by simp)
  lift r to ℕ using hf
  have hNat : n+m ≤ n+r := by exact_mod_cast h
  have hr : m ≤ r := Nat.le_of_add_le_add_left hNat
  exact hn (by exact_mod_cast hr)

/-- Pure cardinal arithmetic for the final exact-rank assembly. -/
theorem summands_exact_of_total_lower_and_upper (r s : Cardinal) (n m : ℕ)
    (hLower : (n+m : Cardinal) ≤ r) (hSum : r=n+s) (hUpper : s≤m) :
    r=n+m ∧ s=m := by
  have hr : r=n+m := le_antisymm (hSum ▸ add_le_add (le_refl (n : Cardinal)) hUpper) hLower
  have hsFinite : s<Cardinal.aleph0 := lt_of_le_of_lt hUpper (by simp)
  have ht := congrArg Cardinal.toNat (hSum.symm.trans hr)
  rw [Cardinal.toNat_add (by simp) hsFinite, Cardinal.toNat_add (by simp) (by simp)] at ht
  simp only [Cardinal.toNat_natCast] at ht
  have hsNat : Cardinal.toNat s=m := Nat.add_left_cancel ht
  refine ⟨hr,?_⟩
  rw [←Cardinal.cast_toNat_of_lt_aleph0 hsFinite,hsNat]

/-- The five printed points give an ordinary integral rank lower bound on
the function-field point group. -/
theorem rank_at_least_five (hMazur : MazurTorsionTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms) :
    (5 : Cardinal) ≤ Module.rank ℤ PointGroup := by
  simpa using (GFunctionField.points_independent hMazur hReduction hFormal).cardinal_lift_le_rank

/-- Five independent Q(G) points, the original rank three and
quadratic character descent force at least two h-twist sections. -/
theorem h_rank_at_least_two (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) :
    (2 : Cardinal) ≤ Module.rank ℤ
      (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point := by
  have hsum := pointGroup_rank_decomposition
  rw [RationalFunctionFamily.rank_eq_three hMazur hMW hDescent hFormal hGT] at hsum
  apply nat_le_of_nat_add_le 3 2
  norm_num only [show (3 : Cardinal)+2=5 by norm_num]
  rw [←hsum]
  exact rank_at_least_five hMazur hReduction hFormal

/-- The checked h-fiber descent bound transports to the h-twist
function-field group through the proved injective specialization. -/
theorem h_rank_at_most_two (hGT : GusicTadic.GusicTadicTheorem11)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point≤2 := by
  obtain ⟨σ,hσ⟩ := GSpecialization.h_injective_normalized_fiber hGT
  exact (σ.toIntLinearMap.rank_le_of_injective hσ).trans
    (GTwistSelmer.curve_rank_at_most_two hMW hDescent)

/-- The Q(G) group has rank five and its h-twist summand has rank two.
The upper bound is the checked local-cover certificate. -/
theorem ranks_exact (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) :
    Module.rank ℤ PointGroup=5 ∧
      Module.rank ℤ (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point=2 := by
  have hsum := pointGroup_rank_decomposition
  rw [RationalFunctionFamily.rank_eq_three hMazur hMW hDescent hFormal hGT] at hsum
  have hLower : (3 : Cardinal)+2≤Module.rank ℤ PointGroup := by
    norm_num only [show (3 : Cardinal)+2=5 by norm_num]
    exact rank_at_least_five hMazur hReduction hFormal
  have h := summands_exact_of_total_lower_and_upper _ _ 3 2 hLower hsum
    (h_rank_at_most_two hGT hMW hDescent)
  norm_num at h
  exact h

theorem rank_eq_five (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) : Module.rank ℤ PointGroup=5 :=
  (ranks_exact hMazur hMW hDescent hReduction hFormal hGT).1

theorem h_rank_eq_two (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) :
    Module.rank ℤ (GusicTadic.genericModel GTwistSelmer.hPolynomial).toAffine.Point=2 :=
  (ranks_exact hMazur hMW hDescent hReduction hFormal hGT).2

/-- The five printed sections span a finite-index subgroup of the
Q(G) group. The finite-generation input is the generic Conrad theorem. -/
theorem printed_five_finite_index (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11)
    (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    (Submodule.span ℤ (Set.range GFunctionField.points)).toAddSubgroup.FiniteIndex := by
  let : Module.Finite ℤ PointGroup := pointGroup_moduleFinite hMWLN
  exact finiteIndex_span_of_rank_eq GFunctionField.points
    (GFunctionField.points_independent hMazur hReduction hFormal)
    (rank_eq_five hMazur hMW hDescent hReduction hFormal hGT)

end
end Z2Z4Rank6.GExactRank
