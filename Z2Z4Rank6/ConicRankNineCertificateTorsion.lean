import Z2Z4Rank6.ConicRankNineCertificateParity
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Torsion generators for the Dujella–Peral rank-nine model. -/
namespace Z2Z4Rank6.ConicRankNineCertificate
noncomputable section

/-- Exact torsion, deduced from the nonsquare-ab descent coordinate. -/
theorem torsion_exact (hMazur : MazurTorsionTheorem) : TorsionExact curve := by
  apply E_torsion_exact hMazur A B factor_nonzero ab_not_square
  rintro ⟨r,hr⟩
  have hp : 0<A*B := by norm_num [A,B]
  nlinarith [mul_self_nonneg r]

theorem two_double : (2 : ℕ) • two=0 := by
  simpa only [two,two_nsmul] using twoLeft_double A B factor_nonzero

theorem four_quadruple : (4 : ℕ) • four=0 := fourPoint_quadruple A B factor_nonzero

theorem two_ne_zero : two≠0 := twoLeft_ne_zero A B factor_nonzero

theorem four_double_ne_zero : (2 : ℕ) • four≠0 := by
  rw [two_nsmul,four,fourPoint_double]
  exact twoZero_ne_zero A B factor_nonzero

theorem generators_independent : two≠(2 : ℕ) • four := by
  rw [two_nsmul,four,fourPoint_double]
  exact twoLeft_ne_twoZero A B factor_nonzero

/-- The displayed two- and four-torsion points generate the entire
rational torsion subgroup. -/
theorem printed_generators (hMazur : MazurTorsionTheorem) :
    AddSubgroup.closure ({two,four} : Set (RationalPoints curve))=
      AddCommGroup.torsion (RationalPoints curve) := by
  classical
  let H := AddSubgroup.closure ({two,four} : Set (RationalPoints curve))
  have hT : two∈H := AddSubgroup.subset_closure (by simp)
  have hQ : four∈H := AddSubgroup.subset_closure (by simp)
  have hle : H≤AddCommGroup.torsion (RationalPoints curve) := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    rcases hP with hP | hP
    · rw [hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by norm_num,two_double⟩
    · rw [Set.mem_singleton_iff.mp hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨4,by norm_num,four_quadruple⟩
  let T : H := ⟨two,hT⟩
  let Q : H := ⟨four,hQ⟩
  obtain ⟨f,hf⟩ := two_four_injective T Q
    (Subtype.ext two_double) (Subtype.ext four_quadruple)
    (fun h => two_ne_zero (congrArg Subtype.val h))
    (fun h => four_double_ne_zero (congrArg Subtype.val h))
    (fun h => generators_independent (congrArg Subtype.val h))
  obtain ⟨e⟩ := torsion_exact hMazur
  have : Finite (AddCommGroup.torsion (RationalPoints curve)) :=
    Finite.of_equiv (ZMod 2×ZMod 4) e.symm.toEquiv
  have : Finite H := Finite.of_injective (AddSubgroup.inclusion hle)
    (AddSubgroup.inclusion_injective hle)
  have hcard : Nat.card (AddCommGroup.torsion (RationalPoints curve))=8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  exact AddSubgroup.eq_of_le_of_card_ge hle (by
    rw [hcard]
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf)

end
end Z2Z4Rank6.ConicRankNineCertificate
