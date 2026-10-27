import Z2Z4Rank6.GJacobianCoordinates
import Z2Z4Rank6.GJacobianTorsion

/-! The printed two independent rational points on J_G, Proposition 7.2(a).
Every torsion-valued integer relation has even coefficients; infinite descent
then proves independence over Z in the point group. -/
namespace Z2Z4Rank6

theorem gJacobian_points_independent (hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem):LinearIndependent ℤ gJacobianPoints := by
  obtain ⟨κ,hκ,_⟩ := hDescent (E (99:ℚ) 49) 0 (-9801) (-2401)
    gJacobianSplit_isElliptic
    (by convert E_eq_splitWeierstrass (99:ℚ) 49 using 1; norm_num)
  let κG : RationalPoints JG →+ (RatSquareClassAdd×RatSquareClassAdd) :=
    κ.comp gJacobianSplitEquiv.toAddMonoidHom
  have hvalues:∀i,κG (gJacobianFourPoints i)=gJacobianBasis i :=
    fun i=>(hκ _).trans (gJacobian_descent_coordinates i)
  have hlin:LinearIndependent (ZMod 2) (fun i=>κG (gJacobianFourPoints i)) := by
    simpa only [hvalues] using gJacobian_basis_independent
  let S:Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
    Submodule.span (ZMod 2) ({κG gJacobianFour,κG gJacobianTwo}:Set _)
  have hspan: AddSubgroup.closure ({gJacobianTwo,gJacobianFour}:Set (RationalPoints JG)) ≤
      S.toAddSubgroup.comap κG := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    change κG P ∈ S
    rcases hP with hP | hP
    · rw [hP]
      exact Submodule.subset_span (by simp)
    · rw [Set.mem_singleton_iff.mp hP]
      exact Submodule.subset_span (by simp)
  have hdiv:∀a:Fin 2→ℤ,IsOfFinAddOrder (∑i,a i • gJacobianPoints i)→∀j,(2:ℤ)∣a j := by
    intro a ha j
    have ht:κG (∑i,a i • gJacobianPoints i) ∈ S := by
      apply hspan
      rw [gJacobian_printed_generators hMazur]
      exact ha
    obtain ⟨u,v,huv⟩ := Submodule.mem_span_pair.mp ht
    have hr:∑i,(a i:ZMod 2) • κG (gJacobianPoints i)=
        u • κG gJacobianFour+v • κG gJacobianTwo := by
      simpa only [map_sum,map_zsmul,Int.cast_smul_eq_zsmul] using huv.symm
    let c:Fin 4→ZMod 2 := ![(a 0:ZMod 2),(a 1:ZMod 2),-u,-v]
    have hz:∑i,c i • κG (gJacobianFourPoints i)=0 := by
      calc
        _ = (∑i,(a i:ZMod 2) • κG (gJacobianPoints i))-
            (u • κG gJacobianFour+v • κG gJacobianTwo) := by
          simp [c,Fin.sum_univ_succ,gJacobianFourPoints,gJacobianPoints]
          match_scalars <;> simp [CharTwo.neg_eq]
        _ = 0 := sub_eq_zero.mpr hr
    have hc:∀i,c i=0 := (Fintype.linearIndependent_iff.mp hlin) c hz
    fin_cases j
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) 2).mp (hc 0)
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) 2).mp (hc 1)
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  exact coefficients_zero_of_torsion_divisibility_at 2 (by decide) gJacobianPoints hdiv n
    (hn ▸ IsOfFinAddOrder.zero)

theorem gJacobian_rank_at_least_two (hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem):2≤Module.rank ℤ (RationalPoints JG) := by
  simpa using
    (gJacobian_points_independent hMazur hDescent).cardinal_le_rank

end Z2Z4Rank6
