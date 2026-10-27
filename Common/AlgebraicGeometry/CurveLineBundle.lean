import Common.AlgebraicGeometry.ConormalCohomologyComparison
import Common.AlgebraicGeometry.ProjectiveLine

/-!
# Invertible modules and projective-line recognition

Invertibility means local O-module trivializations on an
open cover. Degree uses H0 and H1. The recognition input is
Stacks Proposition 53.10.4, tag 0C6U, implication (7) => (1).
-/
namespace Common.AlgebraicGeometry.CurveLineBundle
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ModuleSheafCohomology K3BaseChange
set_option backward.isDefEq.respectTransparency false

def IsInvertible {X : Scheme.{0}} (M : X.Modules) : Prop :=
  ∃ U : X.OpenCover.{0},∀ i,Nonempty
    ((Scheme.Modules.pullback (U.f i)).obj M ≅ SheafOfModules.unit (U.X i).ringCatSheaf)

theorem unit_isInvertible (X : Scheme.{0}) : IsInvertible (SheafOfModules.unit X.ringCatSheaf) := by
  refine ⟨Scheme.coverOfIsIso (P := @IsOpenImmersion) (𝟙 X),fun _=>?_⟩
  exact ⟨(Scheme.Modules.pullbackId X).app (SheafOfModules.unit X.ringCatSheaf)⟩

variable (k : Type) [Field k] (C : Scheme.{0}) (s : C ⟶ Spec (CommRingCat.of k))

def degree (L : C.Modules) : ℤ :=
  euler01 k C s L-euler01 k C s (SheafOfModules.unit C.ringCatSheaf)

def IsProjectiveLine : Prop := Nonempty (Over.mk s ≅ Over.mk (ProjectiveLine.structureMap k))

/-- Stacks Proposition 53.10.4(7) => (1), tag 0C6U. -/
def Stacks0C6U (k : Type) [Field k] : Prop :=
  ∀ (C : Scheme.{0}) (s : C ⟶ Spec (CommRingCat.of k)),
    IsProper s → IsIntegral C → topologicalKrullDim C=1 →
    ∀ L : C.Modules,IsInvertible L → HasFiniteCohomology01 k C s L →
      HasFiniteCohomology01 k C s (SheafOfModules.unit C.ringCatSheaf) →
      Subsingleton (StructureSheafCohomology.Cohomology k C s 1) →
      degree k C s L=1 → IsProjectiveLine k C s

/-- Stacks Lemma 30.8.1 for P1 and O, transported along an
isomorphism over its coefficient field. -/
def Stacks3081 (k : Type) [Field k] : Prop :=
  ∀ (C : Scheme.{0}) (s : C ⟶ Spec (CommRingCat.of k)),
    IsProjectiveLine k C s → Subsingleton (StructureSheafCohomology.Cohomology k C s 1)

/-- The backward implication in EGA IV_2 Proposition 2.5.2(iv), p. 22,
for n=1. This source explicitly includes constant rank n.
The isomorphism to the pullback is retained. -/
def EGAIV2Proposition252iv : Prop :=
  ∀ (X Y : Scheme.{0}) (p : Y ⟶ X),Flat p → Surjective p → QuasiCompact p →
    ∀ (M : X.Modules) (N : Y.Modules),M.IsQuasicoherent →
      Nonempty ((Scheme.Modules.pullback p).obj M ≅ N) →
      IsInvertible N → IsInvertible M

end
end Common.AlgebraicGeometry.CurveLineBundle
