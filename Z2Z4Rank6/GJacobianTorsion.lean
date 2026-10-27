import Z2Z4Rank6.GJacobianBasic
import Mathlib.Algebra.Group.Subgroup.Finite
/-! Printed torsion generators of J_G, Proposition 7.2(a). -/
namespace Z2Z4Rank6
open WeierstrassCurve Affine Affine.Point

theorem gJacobian_torsion_exact (hMazur:MazurTorsionTheorem):TorsionExact JG := by
  obtain ⟨e⟩ := E_torsion_exact hMazur 99 49 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨((gJacobianSplitEquiv.addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr gJacobianSplitEquiv.map_torsion)).trans e⟩

theorem gJacobianFour_double : 2 • gJacobianFour = gJacobianDoubleFour := by
  norm_num [two_nsmul, gJacobianFour, gJacobianDoubleFour, Point.mk, Point.add_def, Point.add,
    negY, slope, addX, addY, negAddY, JG]

theorem gJacobianDoubleFour_double : gJacobianDoubleFour + gJacobianDoubleFour = 0 := by
  apply Point.add_self_of_Y_eq
  norm_num [negY, JG]

theorem gJacobianFour_four : 4 • gJacobianFour = 0 := by
  calc
    4 • gJacobianFour = 2 • gJacobianFour + 2 • gJacobianFour := by abel
    _ = 0 := by rw [gJacobianFour_double]; exact gJacobianDoubleFour_double

theorem gJacobianTwo_two : 2 • gJacobianTwo = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  norm_num [negY, JG]

theorem gJacobianTwo_ne_zero : gJacobianTwo ≠ 0 := Point.some_ne_zero _

theorem gJacobianFour_two_ne_zero : 2 • gJacobianFour ≠ 0 := by
  rw [gJacobianFour_double]
  exact Point.some_ne_zero _

theorem gJacobianGenerators_independent : gJacobianTwo ≠ 2 • gJacobianFour := by
  rw [gJacobianFour_double]
  intro h
  have hx := (Point.some.inj h).1
  norm_num at hx

/-- The two coordinate points printed in Lemma 4.1(b) generate the
whole rational torsion subgroup, under Mazur's generic classification. -/
theorem gJacobian_printed_generators (hMazur : MazurTorsionTheorem) :
    AddSubgroup.closure ({gJacobianTwo,gJacobianFour} : Set (RationalPoints JG)) =
      AddCommGroup.torsion (RationalPoints JG) := by
  classical
  let H := AddSubgroup.closure ({gJacobianTwo,gJacobianFour} : Set (RationalPoints JG))
  have hT : gJacobianTwo ∈ H := AddSubgroup.subset_closure (by simp)
  have hQ : gJacobianFour ∈ H := AddSubgroup.subset_closure (by simp)
  have hle : H ≤ AddCommGroup.torsion (RationalPoints JG) := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    rcases hP with hP | hP
    · rw [hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, gJacobianTwo_two⟩
    · rw [Set.mem_singleton_iff.mp hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨4, by norm_num, gJacobianFour_four⟩
  let T : H := ⟨gJacobianTwo,hT⟩
  let Q : H := ⟨gJacobianFour,hQ⟩
  obtain ⟨f,hf⟩ := two_four_injective T Q
    (Subtype.ext gJacobianTwo_two) (Subtype.ext gJacobianFour_four)
    (fun h => gJacobianTwo_ne_zero (congrArg Subtype.val h))
    (fun h => gJacobianFour_two_ne_zero (congrArg Subtype.val h))
    (fun h => gJacobianGenerators_independent (congrArg Subtype.val h))
  obtain ⟨e⟩ := gJacobian_torsion_exact hMazur
  have : Finite (AddCommGroup.torsion (RationalPoints JG)) :=
    Finite.of_equiv (ZMod 2 × ZMod 4) e.symm.toEquiv
  have : Finite H := Finite.of_injective (AddSubgroup.inclusion hle)
    (AddSubgroup.inclusion_injective hle)
  have hcard : Nat.card (AddCommGroup.torsion (RationalPoints JG)) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  exact AddSubgroup.eq_of_le_of_card_ge hle (by
    rw [hcard]
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf)


end Z2Z4Rank6
