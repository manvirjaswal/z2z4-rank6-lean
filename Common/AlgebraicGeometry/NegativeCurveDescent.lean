module

public import Common.AlgebraicGeometry.ConormalCohomologyComparison
public import Common.AlgebraicGeometry.FiniteDefinitionField

@[expose] public section

/-!
# Negative curves descend along arbitrary algebraically closed extensions

The finite-transcendence-degree restriction in Ellenberg Lemma 4.1 is
removed by EGA IV_2 Proposition 4.8.13 and the proved finite-definition-
field construction. Conormal degrees are reflected using the
cohomology comparisons, not an assigned intersection number.
-/
namespace Common.AlgebraicGeometry.NegativeCurveDescent
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ClosedSubschemeDescent K3BaseChange ConormalCohomologyComparison
set_option backward.isDefEq.respectTransparency false

/-- EGA IV_2 Corollary 4.1.4 p. 54, on the field-extension square. -/
def EGAIV2Corollary414 (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → LocallyOfFiniteType s →
      topologicalKrullDim Y=topologicalKrullDim X

/-- A package of published inputs. -/
structure PublishedInputs : Prop where
  field_definition : ∀ (k K : Type) [Field k] [Field K] [Algebra k K],
    EGAIV2Proposition4813 k K
  dimension : ∀ (k K : Type) [Field k] [Field K] [Algebra k K],
    EGAIV2Corollary414 k K
  negative_finite : ∀ (k K : Type) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K],EllenbergLemma41 k K
  conormal_qc : Stacks01R1ConormalQuasicoherent
  conormal_flat : Stacks0473Conormal
  module_cohomology : ∀ (k K : Type) [Field k] [Field K] [Algebra k K],Stacks02KHModules k K
  structure_cohomology : ∀ (k K : Type) [Field k] [Field K] [Algebra k K],
    Stacks02KHCartesianStructureSheaf k K

variable (H : PublishedInputs) (k K : Type) [Field k] [Field K] [Algebra k K]
  [IsAlgClosed k] [IsAlgClosed K]

include H

/-- Closed negative curves descend. -/
theorem descends (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X)
    (hp : IsPullback p t s (extensionMap k K))
    (hproper : IsProper s) (hprojective : ProjectiveScheme.IsProjective k X s)
    (hsmooth : SmoothOfRelativeDimension 2 s) (hintegral : IsIntegral X)
    (D : ClosedCurve Y) (hD : D.HasNegativeSelfIntersection K t) :
    ∃ C : ClosedCurve X,C.toClosedSubscheme.IsBaseChange D.toClosedSubscheme p := by
  let := hproper
  obtain ⟨L,hL,CL,qL,hqL,hqLfst,hCLD⟩ :=
    H.field_definition k K X Y s t p hp inferInstance inferInstance D.toClosedSubscheme
  let F := FiniteDefinitionField.closure k K L
  let : IsScalarTower k F K := IsScalarTower.of_algebraMap_eq' (by ext a; rfl)
  let : IsProper (K3BaseChange.structureMap k F X s) := by
    dsimp [K3BaseChange.structureMap]
    infer_instance
  let pF : Y ⟶ K3BaseChange.scheme k F X s := intermediateMap k F K hp
  let pFL : K3BaseChange.scheme k F X s ⟶ K3BaseChange.scheme k L X s :=
    towerMap k L F X s
  have hpF : IsPullback pF t (K3BaseChange.structureMap k F X s) (extensionMap F K) :=
    intermediateMap_isPullback k F K hp
  have hcomp : pF≫pFL=qL := by
    apply pullback.hom_ext
    · simpa [pF,pFL,Category.assoc] using hqLfst.symm
    · change pF≫pFL≫K3BaseChange.structureMap k L X s=
        qL≫K3BaseChange.structureMap k L X s
      simpa [pF,pFL,Category.assoc,extensionMap_comp] using hqL.w.symm
  let CFsub := CL.baseChange pFL
  have hCFD : CFsub.IsBaseChange D.toClosedSubscheme pF := by
    apply (CL.baseChange_isBaseChange pFL).cancel
    rw [hcomp]
    exact hCLD
  obtain ⟨qC,hqC⟩ := hCFD.overField F K hpF
  let := D.integral
  have hCFint : IsIntegral CFsub.scheme := integral_reflects F K hqC
  have hCFdim : topologicalKrullDim CFsub.scheme=1 := by
    let := CFsub.closed
    let : LocallyOfFiniteType (CFsub.structureMap (K3BaseChange.structureMap k F X s)) := by
      dsimp [ClosedSubscheme.structureMap]
      infer_instance
    have hd := H.dimension F K _ _ _ _ qC hqC inferInstance
    exact hd.symm.trans D.dimension
  let CF : ClosedCurve (K3BaseChange.scheme k F X s) :=
    {toClosedSubscheme := CFsub,integral := hCFint,dimension := hCFdim}
  have hCFnegative : CF.HasNegativeSelfIntersection F (K3BaseChange.structureMap k F X s) :=
    negative_self_intersection_reflects F K H.conormal_qc H.conormal_flat
      (H.module_cohomology F K) (H.structure_cohomology F K) hpF inferInstance CF D hCFD hD
  obtain ⟨C,hC⟩ := H.negative_finite k F
    (FiniteDefinitionField.closure_finite_trdeg k K L hL)
    X (K3BaseChange.scheme k F X s) s (K3BaseChange.structureMap k F X s)
    (pullback.fst s (extensionMap k F)) (.of_hasPullback _ _)
    hprojective hsmooth hintegral CF hCFnegative
  refine ⟨C,?_⟩
  have h := hC.trans hCFD
  simpa [pF] using h

end
end Common.AlgebraicGeometry.NegativeCurveDescent
