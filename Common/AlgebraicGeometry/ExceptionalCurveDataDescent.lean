import Common.AlgebraicGeometry.NegativeCurveDescent
import Common.AlgebraicGeometry.CurveLineBundle

/-!
# Exceptional-curve data descend

H1 and conormal degree are reflected by tensor comparisons.
Invertibility descends fpqc, and Stacks Proposition 53.10.4(7) => (1)
then recognizes the descended curve as the projective line.
-/
namespace Common.AlgebraicGeometry.ExceptionalCurveDataDescent
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ClosedSubschemeDescent K3BaseChange ConormalCohomologyComparison
open ModuleCohomologyBaseChange CurveLineBundle
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem projective_line_and_degree_one_reflects
    (H : NegativeCurveDescent.PublishedInputs) (hInv : EGAIV2Proposition252iv)
    (hP1 : Stacks0C6U k) (hH1 : Stacks3081 K)
    (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X)
    (hp : IsPullback p t s (extensionMap k K)) (hs : IsProper s)
    (C : ClosedCurve X) (D : ClosedCurve Y)
    (hCD : C.toClosedSubscheme.IsBaseChange D.toClosedSubscheme p)
    (hDline : IsProjectiveLine K D.scheme (D.structureMap t))
    (hDdegree : ConormalDegree.HasDegreeOne D.immersion K (D.structureMap t))
    (hDinv : IsInvertible (ConormalDegree.conormal D.immersion)) :
    IsProjectiveLine k C.scheme (C.structureMap s) ∧
      ConormalDegree.HasDegreeOne C.immersion k (C.structureMap s) := by
  let := hs
  let := C.closed
  let : IsProper (C.structureMap s) := by dsimp [ClosedSubscheme.structureMap]; infer_instance
  let : Flat p := MorphismProperty.of_isPullback hp.flip inferInstance
  obtain ⟨eN⟩ := conormal_comparison k K H.conormal_qc H.conormal_flat
    (H.module_cohomology k K) hp hs _ _ hCD
  obtain ⟨eO⟩ := unit_comparison k K (H.structure_cohomology k K) hp hs _ _ hCD
  have hdegree := conormal_degree_one_reflects k K C.immersion D.immersion _ _ eN eO hDdegree
  obtain ⟨q,hq⟩ := hCD
  have hfield := hq.paste_vert hp
  let : Flat q := MorphismProperty.of_isPullback hfield.flip inferInstance
  let : Surjective q := MorphismProperty.of_isPullback hfield.flip inferInstance
  let : QuasiCompact q := MorphismProperty.of_isPullback hfield.flip inferInstance
  obtain ⟨e⟩ := H.conormal_flat _ _ _ _ C.immersion D.immersion q p hq
    C.closed D.closed inferInstance
  have hCinv := hInv _ _ q inferInstance inferInstance inferInstance
    (ConormalDegree.conormal C.immersion) (ConormalDegree.conormal D.immersion)
    (H.conormal_qc _ _ _ C.closed) ⟨e⟩ hDinv
  have hC1 := h1_descends_of_isPullback k K (H.structure_cohomology k K)
    C.scheme D.scheme (C.structureMap s) (D.structureMap t) q hfield inferInstance
    (hH1 _ _ hDline)
  exact ⟨hP1 _ _ inferInstance C.integral C.dimension _ hCinv hdegree.1.1 hdegree.1.2 hC1
    hdegree.2,hdegree⟩

end
end Common.AlgebraicGeometry.ExceptionalCurveDataDescent
