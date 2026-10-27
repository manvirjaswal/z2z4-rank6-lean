module

public import Z2Z4Rank6.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Tactic

@[expose] public section

/-!
# Passing independence through specialization homomorphisms

These elementary group and finite-set steps assemble the cofinite rank
claims of Jaswal, Theorems 1.2(c) and 8.1(c), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6
noncomputable section

theorem rankAtLeastSix_of_injective_hom {G : Type*} [AddCommGroup G]
    (P : Fin 6 → G) (hP : LinearIndependent ℤ P) (W : WeierstrassCurve ℚ)
    (σ : G →+ RationalPoints W) (hσ : Function.Injective σ) : RankAtLeastSix W := by
  refine ⟨fun i => σ (P i),Fintype.linearIndependent_iff.mpr ?_⟩
  intro a ha
  apply Fintype.linearIndependent_iff.mp hP a
  apply hσ
  simpa only [map_sum,map_zsmul,map_zero] using ha

theorem finite_not_desired_of_finite_failures {A : Type*}
    (W : A → WeierstrassCurve ℚ)
    (hTor : {a | ¬(GoodCurve (W a) ∧ TorsionExact (W a))}.Finite)
    (hRank : {a | ¬RankAtLeastSix (W a)}.Finite) :
    {a | ¬DesiredCurve (W a)}.Finite := by
  apply (hTor.union hRank).subset
  intro a ha
  change ¬(GoodCurve (W a) ∧ TorsionExact (W a)) ∨ ¬RankAtLeastSix (W a)
  change ¬(GoodCurve (W a) ∧ TorsionExact (W a) ∧ RankAtLeastSix (W a)) at ha
  tauto

end
end Z2Z4Rank6
