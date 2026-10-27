module

public import Common.AlgebraicGeometry.CanonicalModulePresentation
public import Common.AlgebraicGeometry.K3CartesianDescent
public import Common.AlgebraicGeometry.FieldBaseChange

@[expose] public section

/-!
# Canonical descent from separate differential and Picard inputs

Stacks Lemma 50.2.1, tag 0FL5, gives pullback of degree-d
differential modules. Stacks Lemma 33.30.3, tag 0CC5, gives Picard
injectivity with its qcqs and finite-H0 hypotheses. Finiteness
for proper schemes is the O_X, i=0 case of Lemma 30.19.2, tag 02O3.

The quasicoherent differential-module presentation is the affine-basis
construction of Section 50.2, Lemma 29.33.5 and Remark 29.33.6. Invertibility
is descended from the unit module with EGA IV_2 Proposition 2.5.2(iv),
p. 22.
-/
namespace Common.AlgebraicGeometry.CanonicalBundleDescent
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Opposite
open CanonicalModulePresentation K3BaseChange
set_option backward.isDefEq.respectTransparency false

/-- Global sections with their structure-map action. -/
def HasFiniteGlobalSections (k : Type) [Field k] (X : Scheme.{0})
    (s : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  letI := (StructureSheafCohomology.scalarMap k X s).toAlgebra
  Module.Finite k (StructureSheafCohomology.GlobalRing X)

/-- Affine-basis construction of Omega^d, Stacks Section 50.2 with
Lemma 29.33.5/Remark 29.33.6. The object is an O-module. -/
def Stacks502DifferentialModule (k : Type) [Field k] : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) (d : ℕ),
    IsProper s → Nonempty {P : Presentation k X s d // P.sheaf.IsQuasicoherent}

/-- Stacks Lemma 50.2.1 (tag 0FL5): differential forms commute with a
cartesian base change, in their affine-basis presentations. -/
def Stacks0FL5 (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → ∀ d : ℕ,
      ∀ (P : Presentation k X s d) (Q : Presentation K Y t d),
        Nonempty ((Scheme.Modules.pullback p).obj P.sheaf ≅ Q.sheaf)

/-- Stacks Lemma 30.19.2, O_X and i=0 over a field. -/
def Stacks02O3Global (k : Type) [Field k] : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)),
    IsProper s → HasFiniteGlobalSections k X s

/-- Kernel-zero case of Stacks Lemma 33.30.3, with qcqs and
finite-dimensional global sections exactly retained. -/
def Stacks0CC5 (k K : Type) [Field k] [Field K] [Algebra k K] : Prop :=
  ∀ (X Y : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ X),
    IsPullback p t s (extensionMap k K) → CompactSpace X → QuasiSeparatedSpace X →
      HasFiniteGlobalSections k X s → ∀ L : X.Modules,CurveLineBundle.IsInvertible L →
        Nonempty ((Scheme.Modules.pullback p).obj L ≅ SheafOfModules.unit Y.ringCatSheaf) →
          Nonempty (L ≅ SheafOfModules.unit X.ringCatSheaf)

theorem canonical_descends (k K : Type) [Field k] [Field K] [Algebra k K]
    (hModule : Stacks502DifferentialModule k)
    (hLineDescent : CurveLineBundle.EGAIV2Proposition252iv)
    (hDifferentials : Stacks0FL5 k K) (hFinite : Stacks02O3Global k)
    (hPicard : Stacks0CC5 k K) : Stacks0CC5And01V0CartesianTopForms k K := by
  intro X Y s t p hpb d hp _hs hCanonical
  obtain ⟨⟨P,hP⟩⟩ := hModule X s d hp
  obtain ⟨e⟩ := hCanonical
  obtain ⟨hPullback⟩ := hDifferentials X Y s t p hpb d P (unitPresentation K Y t d e)
  let : IsProper s := hp
  have hc : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have hq : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s
  let : Flat p := MorphismProperty.of_isPullback hpb.flip inferInstance
  let : Surjective p := MorphismProperty.of_isPullback hpb.flip inferInstance
  let : QuasiCompact p := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hLine := hLineDescent X Y p inferInstance inferInstance inferInstance
    P.sheaf (SheafOfModules.unit Y.ringCatSheaf) hP ⟨hPullback⟩
      (CurveLineBundle.unit_isInvertible Y)
  obtain ⟨hTrivial⟩ := hPicard X Y s t p hpb hc hq (hFinite X s hp)
    P.sheaf hLine ⟨hPullback⟩
  exact trivial_of_module_iso k X s d P hTrivial

end
end Common.AlgebraicGeometry.CanonicalBundleDescent
