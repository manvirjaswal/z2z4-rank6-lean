module

public import Common.AlgebraicGeometry.ModuleCohomologyFunctoriality
public import Common.AlgebraicGeometry.ClosedSubschemeDescent
public import Common.AlgebraicGeometry.K3CartesianDescent
public import Common.AlgebraicGeometry.FieldBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

/-!
# Conormal degree under field extension

The inputs retain three distinct published statements: conormal
quasi-coherence (Stacks Definition 29.32.1, tag 01R1), flat conormal
base change (Lemma 29.32.4, tag 0473), and flat cohomology base change
(Lemma 30.5.2(2), tag 02KH). The linear cohomology transport and degree
reflection below are proved. The cohomology hypothesis explicitly
requires quasi-coherence; no claim is made for arbitrary O-modules.
-/
namespace Common.AlgebraicGeometry.ConormalCohomologyComparison
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ClosedSubschemeDescent ModuleSheafCohomology ModuleCohomologyBaseChange K3BaseChange
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

/-- Quasi-coherence is part of the conormal-sheaf definition in tag 01R1. -/
def Stacks01R1ConormalQuasicoherent : Prop :=
  ∀ (C X : Scheme.{0}) (i : C ⟶ X),IsClosedImmersion i →
    (ConormalDegree.conormal i).IsQuasicoherent

/-- The flat case of Stacks Lemma 29.32.4, tag 0473. -/
def Stacks0473Conormal : Prop :=
  ∀ (C D X Y : Scheme.{0}) (i : C ⟶ X) (j : D ⟶ Y)
    (q : D ⟶ C) (p : Y ⟶ X),
    IsPullback q j i p → IsClosedImmersion i → IsClosedImmersion j → Flat p →
      Nonempty ((Scheme.Modules.pullback q).obj (ConormalDegree.conormal i) ≅
        ConormalDegree.conormal j)

/-- Stacks Lemma 30.5.2(2), tag 02KH, over fields. -/
def Stacks02KHModules : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → QuasiCompact s → QuasiSeparated s →
    ∀ M : X.Modules,M.IsQuasicoherent → ∀ i : ℕ,
      Nonempty ((K ⊗[k] Cohomology k X s M i) ≃ₗ[K]
        Cohomology K Y t ((Scheme.Modules.pullback p).obj M) i)

variable {X Y : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of k)}
  {t : Y ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ X}

theorem conormal_comparison (hQC : Stacks01R1ConormalQuasicoherent)
    (hN : Stacks0473Conormal) (hH : Stacks02KHModules k K)
    (hp : IsPullback p t s (extensionMap k K)) (hs : IsProper s)
    (C : ClosedSubscheme X) (D : ClosedSubscheme Y) (hCD : C.IsBaseChange D p) :
    Nonempty (Comparison k K C.scheme D.scheme (C.structureMap s) (D.structureMap t)
      (ConormalDegree.conormal C.immersion) (ConormalDegree.conormal D.immersion)) := by
  let := hs
  let := C.closed
  let : IsProper (C.structureMap s) := by dsimp [ClosedSubscheme.structureMap]; infer_instance
  let : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨q,hq⟩ := hCD
  obtain ⟨eN⟩ := hN _ _ _ _ C.immersion D.immersion q p hq C.closed D.closed inferInstance
  obtain ⟨e0⟩ := hH _ _ (C.structureMap s) (D.structureMap t) q (hq.paste_vert hp)
    inferInstance inferInstance _ (hQC _ _ _ C.closed) 0
  obtain ⟨e1⟩ := hH _ _ (C.structureMap s) (D.structureMap t) q (hq.paste_vert hp)
    inferInstance inferInstance _ (hQC _ _ _ C.closed) 1
  exact ⟨(Comparison.mk e0 e1).transportRight eN⟩

theorem unit_comparison (hH : Stacks02KHCartesianStructureSheaf k K)
    (hp : IsPullback p t s (extensionMap k K)) (hs : IsProper s)
    (C : ClosedSubscheme X) (D : ClosedSubscheme Y) (hCD : C.IsBaseChange D p) :
    Nonempty (Comparison k K C.scheme D.scheme (C.structureMap s) (D.structureMap t)
      (SheafOfModules.unit C.scheme.ringCatSheaf) (SheafOfModules.unit D.scheme.ringCatSheaf)) := by
  let := hs
  let := C.closed
  let : IsProper (C.structureMap s) := by dsimp [ClosedSubscheme.structureMap]; infer_instance
  obtain ⟨q,hq⟩ := hCD
  obtain ⟨e0⟩ := hH _ _ (C.structureMap s) (D.structureMap t) q (hq.paste_vert hp) inferInstance 0
  obtain ⟨e1⟩ := hH _ _ (C.structureMap s) (D.structureMap t) q (hq.paste_vert hp) inferInstance 1
  exact ⟨⟨e0,e1⟩⟩

theorem negative_self_intersection_reflects (hQC : Stacks01R1ConormalQuasicoherent)
    (hN : Stacks0473Conormal) (hH : Stacks02KHModules k K)
    (hO : Stacks02KHCartesianStructureSheaf k K)
    (hp : IsPullback p t s (extensionMap k K)) (hs : IsProper s)
    (C : ClosedCurve X) (D : ClosedCurve Y)
    (hCD : C.toClosedSubscheme.IsBaseChange D.toClosedSubscheme p)
    (hD : D.HasNegativeSelfIntersection K t) : C.HasNegativeSelfIntersection k s := by
  obtain ⟨eN⟩ := conormal_comparison k K hQC hN hH hp hs _ _ hCD
  obtain ⟨eO⟩ := unit_comparison k K hO hp hs _ _ hCD
  refine ⟨⟨eN.finite_reflects hD.1.1,eO.finite_reflects hD.1.2⟩,?_⟩
  rw [conormal_degree_eq k K C.immersion D.immersion _ _ eN eO]
  exact hD.2

end
end Common.AlgebraicGeometry.ConormalCohomologyComparison
