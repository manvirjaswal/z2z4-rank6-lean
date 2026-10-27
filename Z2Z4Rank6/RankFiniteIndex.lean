import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# Finite index from the full rank of specified points

The final group-theoretic step of Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117. Finite generation is explicit:
equal rank alone does not imply finite index for an arbitrary abelian group.
-/

namespace Z2Z4Rank6

/-- A submodule of a finitely generated abelian group has finite index if it
has the same finite rank as the ambient group. -/
theorem finiteIndex_of_equal_rank
    {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) (n : ℕ)
    (hM : Module.rank ℤ M = n) (hN : Module.rank ℤ N = n) :
    N.toAddSubgroup.FiniteIndex := by
  have hMf : Module.finrank ℤ M = n := Module.finrank_eq_of_rank_eq hM
  have hNf : Module.finrank ℤ N = n := Module.finrank_eq_of_rank_eq hN
  have hqf : Module.finrank ℤ (M ⧸ N) = 0 := by
    have he := N.finrank_quotient_add_finrank
    rw [hMf, hNf] at he
    omega
  have hqt : Module.IsTorsion ℤ (M ⧸ N) :=
    Module.finrank_eq_zero_iff_isTorsion.mp hqf
  have hfinite : Finite (M ⧸ N) := Module.finite_of_fg_torsion _ hqt
  exact AddSubgroup.finiteIndex_iff_finite_quotient.mpr hfinite

/-- A specified independent family has full finite index once the ambient
rank equals its size and the ambient group is finitely generated. -/
theorem finiteIndex_span_of_rank_eq
    {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    {n : ℕ} (P : Fin n → M) (hP : LinearIndependent ℤ P)
    (hrank : Module.rank ℤ M = n) :
    (Submodule.span ℤ (Set.range P)).toAddSubgroup.FiniteIndex := by
  apply finiteIndex_of_equal_rank _ n hrank
  classical
  have : Finite (Set.range P) := (Set.finite_range P).to_subtype
  let : Fintype (Set.range P) := Fintype.ofFinite _
  have hcard : Fintype.card (Set.range P) = n := by
    simpa using (Fintype.card_congr (Equiv.ofInjective P hP.injective)).symm
  rw [rank_span hP, Cardinal.mk_fintype, hcard]

end Z2Z4Rank6
