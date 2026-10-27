import Z2Z4Rank6.SecondJacobianDescent
import Z2Z4Rank6.SecondJacobianTorsion

/-! The printed two independent rational points on J_G, Theorem 8.1(a).
Every torsion-valued integer relation has even coefficients; infinite descent
then proves independence over Z in the point group. -/
namespace Z2Z4Rank6

theorem secondJacobian_points_independent (hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem):LinearIndependent ℤ secondJacobianPoints := by
  obtain ⟨κ,hκ,_⟩ := hDescent J2 (-102809641014) 51068871386 51740769627
    secondJacobian_isElliptic secondJacobian_eq_split
  let κG : RationalPoints J2 →+ (RatSquareClassAdd×RatSquareClassAdd) := κ
  have hvalues:∀i,κG (secondJacobianFourPoints i)=secondJacobianBasis i :=
    fun i=>(hκ _).trans (secondJacobian_descent_coordinates i)
  have hlin:LinearIndependent (ZMod 2) (fun i=>κG (secondJacobianFourPoints i)) := by
    simpa only [hvalues] using secondJacobian_basis_independent
  let S:Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
    Submodule.span (ZMod 2) ({κG secondJacobianFour,κG secondJacobianTwo}:Set _)
  have hspan: AddSubgroup.closure ({secondJacobianTwo,secondJacobianFour}:Set (RationalPoints J2)) ≤
      S.toAddSubgroup.comap κG := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    change κG P ∈ S
    rcases hP with hP | hP
    · rw [hP]
      exact Submodule.subset_span (by simp)
    · rw [Set.mem_singleton_iff.mp hP]
      exact Submodule.subset_span (by simp)
  have hdiv:∀a:Fin 2→ℤ,IsOfFinAddOrder (∑i,a i • secondJacobianPoints i)→∀j,(2:ℤ)∣a j := by
    intro a ha j
    have ht:κG (∑i,a i • secondJacobianPoints i) ∈ S := by
      apply hspan
      rw [secondJacobian_printed_generators hMazur]
      exact ha
    obtain ⟨u,v,huv⟩ := Submodule.mem_span_pair.mp ht
    have hr:∑i,(a i:ZMod 2) • κG (secondJacobianPoints i)=
        u • κG secondJacobianFour+v • κG secondJacobianTwo := by
      simpa only [map_sum,map_zsmul,Int.cast_smul_eq_zsmul] using huv.symm
    let c:Fin 4→ZMod 2 := ![(a 0:ZMod 2),(a 1:ZMod 2),-u,-v]
    have hz:∑i,c i • κG (secondJacobianFourPoints i)=0 := by
      calc
        _ = (∑i,(a i:ZMod 2) • κG (secondJacobianPoints i))-
            (u • κG secondJacobianFour+v • κG secondJacobianTwo) := by
          simp [c,Fin.sum_univ_succ,secondJacobianFourPoints,secondJacobianPoints]
          match_scalars <;> simp [CharTwo.neg_eq]
        _ = 0 := sub_eq_zero.mpr hr
    have hc:∀i,c i=0 := (Fintype.linearIndependent_iff.mp hlin) c hz
    fin_cases j
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) 2).mp (hc 0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) 2).mp (hc 1)
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact coefficients_zero_of_torsion_divisibility_at 2 (by decide) secondJacobianPoints hdiv n
    (hn ▸ IsOfFinAddOrder.zero)

theorem secondJacobian_rank_at_least_two (hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem):2≤Module.rank ℤ (RationalPoints J2) := by
  simpa using
    (secondJacobian_points_independent hMazur hDescent).cardinal_le_rank

end Z2Z4Rank6
