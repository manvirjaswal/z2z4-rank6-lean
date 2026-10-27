module

public import Z2Z4Rank6.GJacobianRankLower
public import Z2Z4Rank6.GJacobianSelmer
public import Z2Z4Rank6.SplitDescentImage
public import Z2Z4Rank6.ECExactRank

@[expose] public section

/-!
# Rank two of the printed J_G equation

The complete local certificate gives 16 classes, attained by the two printed
points and two torsion generators. Full rational two-torsion and the
generic Mordell--Weil theorem then give ordinary rank at most 2. The checked
printed-point independence supplies the lower bound. This is the arithmetic
part of Jaswal Proposition 7.2(a), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6

theorem gJacobian_descent_image_eq_full
    (κ : RationalPoints JG →+ (RatSquareClassAdd×RatSquareClassAdd))
    (hκ : ∀P,κ P=completeDescentCoordinates (E 99 49) 0 (-9801) (-2401) (gJacobianSplitEquiv P)):
    (κ.range:Set (RatSquareClassAdd×RatSquareClassAdd))=fullTwoSelmerClasses 9801 2401 := by
  rw [gJacobian_fullTwoSelmerClasses_eq_space]
  have hlower:gJacobianSelmerSpace≤AddSubgroup.toZModSubmodule 2 κ.range := by
    apply Submodule.span_le.mpr
    rintro q ⟨i,rfl⟩
    change gJacobianBasis i∈κ.range
    exact ⟨gJacobianFourPoints i,(hκ _).trans (gJacobian_descent_coordinates i)⟩
  apply Set.Subset.antisymm
  · rintro q ⟨P,rfl⟩
    rw [hκ,←gJacobian_fullTwoSelmerClasses_eq_space]
    exact split_completeDescent_coordinates_mem (E (99:ℚ) 49) 9801 2401
      (by norm_num) (by norm_num) (by norm_num)
      (by convert E_eq_splitWeierstrass (99:ℚ) 49 using 1; norm_num) _
  · exact hlower

theorem gJacobian_descent_image_exact (hDescent:CompleteTwoDescentTheorem):
    ∃κ:RationalPoints JG→+(RatSquareClassAdd×RatSquareClassAdd),
      (∀P,κ P=completeDescentCoordinates (E 99 49) 0 (-9801) (-2401) (gJacobianSplitEquiv P)) ∧
      (∀P,κ P=0 ↔ ∃Q:RationalPoints JG,(2:ℕ) • Q=P) ∧ Nat.card κ.range=16 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent (E (99:ℚ) 49) 0 (-9801) (-2401)
    gJacobianSplit_isElliptic (by convert E_eq_splitWeierstrass (99:ℚ) 49 using 1; norm_num)
  let κG:RationalPoints JG→+(RatSquareClassAdd×RatSquareClassAdd) :=
    κ.comp gJacobianSplitEquiv.toAddMonoidHom
  have hval:∀P,κG P=completeDescentCoordinates (E 99 49) 0 (-9801) (-2401) (gJacobianSplitEquiv P) :=
    fun P=>hκ _
  refine ⟨κG,hval,?_,?_⟩
  · intro P
    change κ (gJacobianSplitEquiv P)=0 ↔ _
    rw [hker]
    constructor
    · rintro ⟨Q,hQ⟩
      refine ⟨gJacobianSplitEquiv.symm Q,gJacobianSplitEquiv.injective ?_⟩
      simpa only [map_nsmul,AddEquiv.apply_symm_apply] using hQ
    · rintro ⟨Q,rfl⟩
      exact ⟨gJacobianSplitEquiv Q,(map_nsmul gJacobianSplitEquiv 2 Q).symm⟩
  · change (κG.range:Set (RatSquareClassAdd×RatSquareClassAdd)).ncard=16
    rw [gJacobian_descent_image_eq_full κG hval,gJacobian_fullTwoSelmerClasses_card]

theorem gJacobian_fullTwoTorsion_inclusion:
    ∃j:(ZMod 2×ZMod 2)→+RationalPoints JG,Function.Injective j := by
  obtain ⟨f,hf⟩ := E_two_four_inclusion 99 49 (by norm_num)
  refine ⟨gJacobianSplitEquiv.symm.toAddMonoidHom.comp (f.comp twoTwoToTwoFour),?_⟩
  exact gJacobianSplitEquiv.symm.injective.comp (hf.comp twoTwoToTwoFour_injective)

theorem gJacobian_doubling_quotient_card(hDescent:CompleteTwoDescentTheorem):
    Nat.card (RankModTwo.DoublingQuotient (RationalPoints JG))=16 := by
  obtain ⟨κ,_,hker,hcard⟩ := gJacobian_descent_image_exact hDescent
  rw [RankModTwo.card_doubling_eq_range κ hker,hcard]

theorem gJacobian_rank_at_most_two(hMW:MordellWeilTheorem)(hDescent:CompleteTwoDescentTheorem):
    Module.rank ℤ (RationalPoints JG)≤2 := by
  let : AddGroup.FG (RationalPoints JG) := hMW JG inferInstance
  obtain ⟨κ,_,hker,hcard⟩ := gJacobian_descent_image_exact hDescent
  obtain ⟨j,hj⟩ := gJacobian_fullTwoTorsion_inclusion
  apply RankModTwo.rank_le_of_descent_image_card κ hker j hj 2
  change Nat.card κ.range ≤ 16
  exact hcard.le

theorem gJacobian_rank_eq_two(hMW:MordellWeilTheorem)(hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem):Module.rank ℤ (RationalPoints JG)=2 :=
  le_antisymm (gJacobian_rank_at_most_two hMW hDescent) (gJacobian_rank_at_least_two hMazur hDescent)

end Z2Z4Rank6
