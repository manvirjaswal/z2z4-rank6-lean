import Common.AlgebraicGeometry.ConormalDegree
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Consequences of cohomology base-change comparisons

The comparison data retain the tensor products of sheaf
cohomology groups. Euler characteristic and conormal degree invariance
are proved from these data.
-/
namespace Common.AlgebraicGeometry.ModuleCohomologyBaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory ModuleSheafCohomology
open scoped TensorProduct
variable (k K : Type) [Field k] [Field K] [Algebra k K]

structure Comparison (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (N : Y.Modules) where
  zero : (K ⊗[k] Cohomology k X s M 0) ≃ₗ[K] Cohomology K Y t N 0
  one : (K ⊗[k] Cohomology k X s M 1) ≃ₗ[K] Cohomology K Y t N 1

theorem finite_of_finite_baseChange (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional K (K ⊗[k] V)] : FiniteDimensional k V := by
  apply Module.rank_lt_aleph0_iff.mp
  have h := Module.rank_lt_aleph0 K (K ⊗[k] V)
  simpa only [Module.rank_baseChange,Cardinal.lift_id] using h

variable {k K} {X Y : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of k)}
  {t : Y ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N : Y.Modules}

theorem Comparison.euler_eq (e : Comparison k K X Y s t M N) :
    euler01 k X s M=euler01 K Y t N := by
  simp only [euler01,←e.zero.finrank_eq,←e.one.finrank_eq,Module.finrank_baseChange]

theorem Comparison.finite_reflects (e : Comparison k K X Y s t M N)
    (h : HasFiniteCohomology01 K Y t N) : HasFiniteCohomology01 k X s M := by
  obtain ⟨h0,h1⟩ := h
  constructor
  · let := h0
    let : FiniteDimensional K (K ⊗[k] Cohomology k X s M 0) :=
      FiniteDimensional.of_injective e.zero.toLinearMap e.zero.injective
    exact finite_of_finite_baseChange k K _
  · let := h1
    let : FiniteDimensional K (K ⊗[k] Cohomology k X s M 1) :=
      FiniteDimensional.of_injective e.one.toLinearMap e.one.injective
    exact finite_of_finite_baseChange k K _

variable (k K) {C D X' Y' : Scheme.{0}} (i : C ⟶ X') (j : D ⟶ Y')
  (c : C ⟶ Spec (CommRingCat.of k)) (d : D ⟶ Spec (CommRingCat.of K))

theorem conormal_degree_eq
    (eN : Comparison k K C D c d (ConormalDegree.conormal i) (ConormalDegree.conormal j))
    (eO : Comparison k K C D c d (SheafOfModules.unit C.ringCatSheaf)
      (SheafOfModules.unit D.ringCatSheaf)) :
    ConormalDegree.degree i k c=ConormalDegree.degree j K d := by
  unfold ConormalDegree.degree
  rw [eN.euler_eq,eO.euler_eq]

theorem conormal_degree_one_reflects
    (eN : Comparison k K C D c d (ConormalDegree.conormal i) (ConormalDegree.conormal j))
    (eO : Comparison k K C D c d (SheafOfModules.unit C.ringCatSheaf)
      (SheafOfModules.unit D.ringCatSheaf))
    (h : ConormalDegree.HasDegreeOne j K d) : ConormalDegree.HasDegreeOne i k c := by
  refine ⟨⟨eN.finite_reflects h.1.1,eO.finite_reflects h.1.2⟩,?_⟩
  rw [conormal_degree_eq k K i j c d eN eO]
  exact h.2

end
end Common.AlgebraicGeometry.ModuleCohomologyBaseChange
