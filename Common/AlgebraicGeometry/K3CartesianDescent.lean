module

public import Common.AlgebraicGeometry.K3BaseChange

@[expose] public section

/-!
# K3 descent on a cartesian field-extension diagram

Stacks Lemma 30.5.2(2), tag 02KH, is expressed on the cartesian
diagram. Canonical-triviality reflection records a property of the
top differential line. CanonicalBundleDescent.canonical_descends proves that
property from the separate differential-base-change, finite-global-section,
line-bundle-descent and Picard inputs. The canonical-property argument of
descends_of_isPullback is supplied by that proved theorem in the surface
applications.
-/
namespace Common.AlgebraicGeometry.K3BaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (k K : Type) [Field k] [Field K] [Algebra k K]

def Stacks02KHCartesianStructureSheaf : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → IsProper s → ∀ i : ℕ,
      Nonempty ((K ⊗[k] StructureSheafCohomology.Cohomology k X s i) ≃ₗ[K]
        StructureSheafCohomology.Cohomology K Y t i)

/-- Canonical-triviality reflection for the top differential line.
`CanonicalBundleDescent.canonical_descends` proves this property from its
separate named hypotheses; the surface theorems supply that proved result. -/
def Stacks0CC5And01V0CartesianTopForms : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → ∀ d : ℕ,
      IsProper s → SmoothOfRelativeDimension d s →
      AffineDifferentialForms.HasTrivialCanonical K Y t d →
        AffineDifferentialForms.HasTrivialCanonical k X s d

theorem h1_descends_of_isPullback (h : Stacks02KHCartesianStructureSheaf k K)
    (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X)
    (hpb : IsPullback p t s (extensionMap k K)) (hp : IsProper s)
    (h1 : Subsingleton (StructureSheafCohomology.Cohomology K Y t 1)) :
    Subsingleton (StructureSheafCohomology.Cohomology k X s 1) := by
  let := h1
  obtain ⟨e⟩ := h X Y s t p hpb hp 1
  refine ⟨fun a b=>?_⟩
  apply Module.Flat.tensorProduct_mk_injective k
    (StructureSheafCohomology.Cohomology k X s 1) K
  apply e.injective
  exact Subsingleton.elim _ _

theorem descends_of_isPullback (hCoh : Stacks02KHCartesianStructureSheaf k K)
    (hForms : Stacks0CC5And01V0CartesianTopForms k K)
    (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X)
    (hpb : IsPullback p t s (extensionMap k K))
    (hp : IsProper s) (hs : SmoothOfRelativeDimension 2 s)
    (hi : GeometricallyIntegral s) (hd : topologicalKrullDim X=2)
    (h : IsK3 K Y t) : IsK3 k X s :=
  ⟨hp,hs,hi,hd,hForms X Y s t p hpb 2 hp hs h.canonical,
    h1_descends_of_isPullback k K hCoh X Y s t p hpb hp h.h1_vanishes⟩

end
end Common.AlgebraicGeometry.K3BaseChange
