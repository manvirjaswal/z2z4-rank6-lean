import Z2Z4Rank6.SecondExampleRankSevenTorsion

/-!
# Rank at least seven of the printed second example

The unnumbered assertion following Theorem 8.1 in Jaswal,
DOI 10.5281/zenodo.23437117. The seven rational points have independent
complete-descent images modulo the torsion span. Every torsion-valued
integer relation therefore has even coefficients; integral descent proves
independence.
-/
namespace Z2Z4Rank6.SecondExampleRankSeven
noncomputable section

/-- The seven specified rational points are integer-linearly independent. -/
theorem points_independent (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) : LinearIndependent ℤ points := by
  obtain ⟨κ,hκ,_⟩ := hDescent curve 0 (-(A^2)) (-(B^2))
    curveElliptic (E_eq_splitWeierstrass A B)
  have hvalues : ∀i,κ (ninePoints i)=squareclasses i :=
    fun i => (hκ _).trans (descent_coordinates i)
  have hlin : LinearIndependent (ZMod 2) (fun i => κ (ninePoints i)) := by
    simpa only [hvalues] using squareclasses_independent
  let S : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
    Submodule.span (ZMod 2) ({κ two,κ four} : Set _)
  have hspan : AddSubgroup.closure ({two,four} : Set (RationalPoints curve))≤
      S.toAddSubgroup.comap κ := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    change κ P∈S
    rcases hP with hP | hP
    · rw [hP]
      exact Submodule.subset_span (by simp)
    · rw [Set.mem_singleton_iff.mp hP]
      exact Submodule.subset_span (by simp)
  have hdiv : ∀a : Fin 7→ℤ,IsOfFinAddOrder (∑i,a i • points i)→∀j,(2:ℤ)∣a j := by
    intro a ha j
    have ht : κ (∑i,a i • points i)∈S := by
      apply hspan
      rw [printed_generators hMazur]
      exact ha
    obtain ⟨u,v,huv⟩ := Submodule.mem_span_pair.mp ht
    have hr : ∑i,(a i : ZMod 2) • κ (points i)=u • κ two+v • κ four := by
      simpa only [map_sum,map_zsmul,Int.cast_smul_eq_zsmul] using huv.symm
    let c : Fin 9→ZMod 2 :=
      ![(a 0 : ZMod 2),(a 1 : ZMod 2),(a 2 : ZMod 2),(a 3 : ZMod 2),
        (a 4 : ZMod 2),(a 5 : ZMod 2),(a 6 : ZMod 2),-u,-v]
    have hz : ∑i,c i • κ (ninePoints i)=0 := by
      calc
        _ = (∑i,(a i : ZMod 2) • κ (points i))-(u • κ two+v • κ four) := by
          simp [c,Fin.sum_univ_succ,ninePoints]
          match_scalars <;> simp [CharTwo.neg_eq]
        _ = 0 := sub_eq_zero.mpr hr
    have hc : ∀i,c i=0 := (Fintype.linearIndependent_iff.mp hlin) c hz
    fin_cases j
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) 2).mp (hc 0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) 2).mp (hc 1)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 2) 2).mp (hc 2)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 3) 2).mp (hc 3)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 4) 2).mp (hc 4)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 5) 2).mp (hc 5)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 6) 2).mp (hc 6)
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact coefficients_zero_of_torsion_divisibility_at 2 (by decide) points hdiv n
    (hn ▸ IsOfFinAddOrder.zero)

/-- The printed curve E_{460019200,11180308689} has ordinary integral
rank at least seven. Exact rank and Sha[2] are proved in SecondExampleRankSevenExact
and SecondExampleRankSevenSha. -/
theorem rank_at_least_seven (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    7≤Module.rank ℤ (RationalPoints curve) := by
  simpa using (points_independent hMazur hDescent).cardinal_le_rank

end
end Z2Z4Rank6.SecondExampleRankSeven
