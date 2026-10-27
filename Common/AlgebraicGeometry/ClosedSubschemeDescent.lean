import Common.AlgebraicGeometry.K3BaseChange
import Common.AlgebraicGeometry.ProjectiveScheme
import Common.AlgebraicGeometry.ConormalDegree
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Closed subschemes and their fields of definition

A descent datum retains schemes, closed immersions and a
cartesian square. The field-of-definition input is EGA IV_2,
Proposition 4.8.13, for a closed subscheme of a finite-type scheme.
The negative-curve input is Ellenberg, Endomorphism Algebras of
Jacobians, Lemma 4.1, author PDF p. 14 (proof p. 15). Its finite
transcendence degree assumption is retained explicitly.
-/
namespace Common.AlgebraicGeometry.ClosedSubschemeDescent
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open K3BaseChange
set_option backward.isDefEq.respectTransparency false

structure ClosedSubscheme (X : Scheme.{0}) where
  scheme : Scheme.{0}
  immersion : scheme ⟶ X
  closed : IsClosedImmersion immersion

namespace ClosedSubscheme
variable {X Y Z : Scheme.{0}}

def baseChange (C : ClosedSubscheme X) (p : Y ⟶ X) : ClosedSubscheme Y where
  scheme := pullback C.immersion p
  immersion := pullback.snd C.immersion p
  closed := by let := C.closed; infer_instance


def structureMap (C : ClosedSubscheme X) {k : Type} [Field k]
    (s : X ⟶ Spec (CommRingCat.of k)) : C.scheme ⟶ Spec (CommRingCat.of k) :=
  C.immersion≫s

/-- Equality with a pullback closed subscheme. -/
def IsBaseChange (C : ClosedSubscheme X) (D : ClosedSubscheme Y) (p : Y ⟶ X) : Prop :=
  ∃ q : D.scheme ⟶ C.scheme,IsPullback q D.immersion C.immersion p

theorem baseChange_isBaseChange (C : ClosedSubscheme X) (p : Y ⟶ X) :
    C.IsBaseChange (C.baseChange p) p := ⟨pullback.fst _ _,.of_hasPullback _ _⟩

theorem IsBaseChange.trans {C : ClosedSubscheme X} {D : ClosedSubscheme Y}
    {E : ClosedSubscheme Z} {p : Y ⟶ X} {q : Z ⟶ Y}
    (hCD : C.IsBaseChange D p) (hDE : D.IsBaseChange E q) :
    C.IsBaseChange E (q≫p) := by
  obtain ⟨f,hf⟩ := hCD
  obtain ⟨g,hg⟩ := hDE
  exact ⟨g≫f,hg.paste_horiz hf⟩

theorem IsBaseChange.cancel {C : ClosedSubscheme X} {D : ClosedSubscheme Y}
    {E : ClosedSubscheme Z} {p : Y ⟶ X} {q : Z ⟶ Y}
    (hCD : C.IsBaseChange D p) (hCE : C.IsBaseChange E (q≫p)) :
    D.IsBaseChange E q := by
  obtain ⟨f,hf⟩ := hCD
  obtain ⟨g,hg⟩ := hCE
  exact ⟨_,hg.of_right' hf⟩

variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem IsBaseChange.overField {C : ClosedSubscheme X} {D : ClosedSubscheme Y}
    {p : Y ⟶ X} {s : X ⟶ Spec (CommRingCat.of k)}
    {t : Y ⟶ Spec (CommRingCat.of K)}
    (h : C.IsBaseChange D p) (hp : IsPullback p t s (extensionMap k K)) :
    ∃ q : D.scheme ⟶ C.scheme,
      IsPullback q (D.structureMap t) (C.structureMap s) (extensionMap k K) := by
  obtain ⟨q,hq⟩ := h
  exact ⟨q,hq.paste_vert hp⟩

end ClosedSubscheme

structure ClosedCurve (X : Scheme.{0}) extends ClosedSubscheme X where
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme=1

namespace ClosedCurve
variable {X : Scheme.{0}} (C : ClosedCurve X) (k : Type) [Field k]
  (s : X ⟶ Spec (CommRingCat.of k))

def HasNegativeSelfIntersection : Prop :=
  ConormalDegree.HasFiniteCohomology C.immersion k (C.structureMap s) ∧
    0<ConormalDegree.degree C.immersion k (C.structureMap s)

end ClosedCurve

variable (k K : Type) [Field k] [Field K] [Algebra k K]

/-- EGA IV_2 Proposition 4.8.13, closed-subscheme case. A field of
finite type is retained as a finitely generated intermediate
field. Minimality of the field of definition is not needed here. -/
def EGAIV2Proposition4813 : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → LocallyOfFiniteType s → QuasiCompact s →
    ∀ D : ClosedSubscheme Y,∃ L : IntermediateField k K,L.FG ∧
      ∃ C : ClosedSubscheme (K3BaseChange.scheme k L X s),
        ∃ q : Y ⟶ K3BaseChange.scheme k L X s,
          IsPullback q t (K3BaseChange.structureMap k L X s) (extensionMap L K) ∧
          q≫pullback.fst s (extensionMap k L)=p ∧ C.IsBaseChange D q

/-- Ellenberg Lemma 4.1, author PDF p. 14. The self-intersection is
written as minus the degree of the conormal line. On a smooth
surface an integral closed curve is an effective Cartier divisor. -/
def EllenbergLemma41 [IsAlgClosed k] [IsAlgClosed K] : Prop :=
  Algebra.trdeg k K<Cardinal.aleph0 →
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → ProjectiveScheme.IsProjective k X s →
    SmoothOfRelativeDimension 2 s → IsIntegral X →
    ∀ D : ClosedCurve Y,D.HasNegativeSelfIntersection K t →
      ∃ C : ClosedCurve X,C.toClosedSubscheme.IsBaseChange D.toClosedSubscheme p

end
end Common.AlgebraicGeometry.ClosedSubschemeDescent
