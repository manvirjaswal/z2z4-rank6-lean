import Z2Z4Rank6.SecondJacobianHalving
import Mathlib.Algebra.Group.Subgroup.Finite
/-! Printed torsion generators of J_G2, Theorem 8.1(a). -/
namespace Z2Z4Rank6
open WeierstrassCurve Affine Affine.Point

theorem secondJacobian_torsion_exact (hMazur:MazurTorsionTheorem):TorsionExact J2 := by
  have he : TorsionExact (E (393129:ℚ) 25921) := by
    obtain ⟨f,hf⟩ := E_torsion_two_four_inclusion 393129 25921 (by norm_num)
    apply two_four_equiv_of_mazur (hMazur (E 393129 25921) secondJacobianSplit_isElliptic) f hf
    rintro ⟨Q,hQ⟩
    apply secondJacobian_no_order_eight_of_shift 393129 25921 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    refine ⟨Q.val,?_⟩
    exact (addOrderOf_injective ((AddCommGroup.torsion (RationalPoints (E (393129:ℚ) 25921))).subtype)
      Subtype.coe_injective Q).trans hQ
  obtain ⟨e⟩ := he
  exact ⟨((secondJacobianSplitEquiv.addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr secondJacobianSplitEquiv.map_torsion)).trans e⟩

theorem secondJacobianFour_double : 2 • secondJacobianFour = secondJacobianDoubleFour := by
  norm_num [two_nsmul, secondJacobianFour, secondJacobianDoubleFour, Point.mk, Point.add_def, Point.add,
    negY, slope, addX, addY, negAddY, J2]

theorem secondJacobianDoubleFour_double : secondJacobianDoubleFour + secondJacobianDoubleFour = 0 := by
  apply Point.add_self_of_Y_eq
  norm_num [negY, J2]

theorem secondJacobianFour_four : 4 • secondJacobianFour = 0 := by
  calc
    4 • secondJacobianFour = 2 • secondJacobianFour + 2 • secondJacobianFour := by abel
    _ = 0 := by rw [secondJacobianFour_double]; exact secondJacobianDoubleFour_double

theorem secondJacobianTwo_two : 2 • secondJacobianTwo = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  norm_num [negY, J2]

theorem secondJacobianTwo_ne_zero : secondJacobianTwo ≠ 0 := Point.some_ne_zero _

theorem secondJacobianFour_two_ne_zero : 2 • secondJacobianFour ≠ 0 := by
  rw [secondJacobianFour_double]
  exact Point.some_ne_zero _

theorem secondJacobianGenerators_independent : secondJacobianTwo ≠ 2 • secondJacobianFour := by
  rw [secondJacobianFour_double]
  intro h
  have hx := (Point.some.inj h).1
  norm_num at hx

/-- The two coordinate points printed in Lemma 4.1(b) generate the
whole rational torsion subgroup, under Mazur's generic classification. -/
theorem secondJacobian_printed_generators (hMazur : MazurTorsionTheorem) :
    AddSubgroup.closure ({secondJacobianTwo,secondJacobianFour} : Set (RationalPoints J2)) =
      AddCommGroup.torsion (RationalPoints J2) := by
  classical
  let H := AddSubgroup.closure ({secondJacobianTwo,secondJacobianFour} : Set (RationalPoints J2))
  have hT : secondJacobianTwo ∈ H := AddSubgroup.subset_closure (by simp)
  have hQ : secondJacobianFour ∈ H := AddSubgroup.subset_closure (by simp)
  have hle : H ≤ AddCommGroup.torsion (RationalPoints J2) := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    rcases hP with hP | hP
    · rw [hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, secondJacobianTwo_two⟩
    · rw [Set.mem_singleton_iff.mp hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨4, by norm_num, secondJacobianFour_four⟩
  let T : H := ⟨secondJacobianTwo,hT⟩
  let Q : H := ⟨secondJacobianFour,hQ⟩
  obtain ⟨f,hf⟩ := two_four_injective T Q
    (Subtype.ext secondJacobianTwo_two) (Subtype.ext secondJacobianFour_four)
    (fun h => secondJacobianTwo_ne_zero (congrArg Subtype.val h))
    (fun h => secondJacobianFour_two_ne_zero (congrArg Subtype.val h))
    (fun h => secondJacobianGenerators_independent (congrArg Subtype.val h))
  obtain ⟨e⟩ := secondJacobian_torsion_exact hMazur
  have : Finite (AddCommGroup.torsion (RationalPoints J2)) :=
    Finite.of_equiv (ZMod 2 × ZMod 4) e.symm.toEquiv
  have : Finite H := Finite.of_injective (AddSubgroup.inclusion hle)
    (AddSubgroup.inclusion_injective hle)
  have hcard : Nat.card (AddCommGroup.torsion (RationalPoints J2)) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  exact AddSubgroup.eq_of_le_of_card_ge hle (by
    rw [hcard]
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf)


end Z2Z4Rank6
