module

public import Common.AlgebraicGeometry.AffineDifferentialForms
public import Common.AlgebraicGeometry.CurveLineBundle

@[expose] public section

/-!
# Module presentations of differential forms

A presentation consists of an O-module, affine-coordinate
exterior-power isomorphisms, and restriction compatibility on the
canonical spanning wedges. This is the affine-basis description of
Omega^d in Stacks Section 50.2 and Lemma 29.33.5/Remark 29.33.6.

An isomorphism of this module to O gives a compatible affine
trivialization by composition. Conversely a compatible trivialization
itself presents the unit module. Both statements are proved.
-/
namespace Common.AlgebraicGeometry.CanonicalModulePresentation
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Opposite
open AffineDifferentialForms
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) (d : ℕ)

instance sectionsModule (M : X.Modules) (U : X.Opens) :
    Module (sections k X s U) Γ(M,U) := by
  dsimp [sections]
  infer_instance

structure Presentation where
  sheaf : X.Modules
  affine : ∀ (U : X.Opens),IsAffineOpen U →
    Forms k X s U d ≃ₗ[sections k X s U] Γ(sheaf,U)
  compatible : ∀ (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V≤U) (a : Fin d → sections k X s U),
    sheaf.presheaf.map (homOfLE h).op
      (affine U hU (exteriorPower.ιMulti (sections k X s U) d
        (fun i=>KaehlerDifferential.D k (sections k X s U) (a i)))) =
    affine V hV (exteriorPower.ιMulti (sections k X s V) d
      (fun i=>KaehlerDifferential.D k (sections k X s V)
        (restriction k X s U V h (a i))))

def unitPresentation (h : CanonicalTrivialization k X s d) : Presentation k X s d where
  sheaf := SheafOfModules.unit X.ringCatSheaf
  affine := h.coefficient
  compatible := h.compatible

theorem trivial_of_module_iso (P : Presentation k X s d)
    (e : P.sheaf ≅ SheafOfModules.unit X.ringCatSheaf) : HasTrivialCanonical k X s d := by
  refine ⟨⟨fun U hU => (P.affine U hU).trans
    (((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso e).toLinearEquiv),?_⟩⟩
  intro U V hU hV h a
  change X.presheaf.map (homOfLE h).op
      (e.hom.app U (P.affine U hU _)) = e.hom.app V (P.affine V hV _)
  have hn := ConcreteCategory.congr_hom
    (e.hom.mapPresheaf.naturality (homOfLE h).op)
    (P.affine U hU (exteriorPower.ιMulti (sections k X s U) d
      (fun i=>KaehlerDifferential.D k (sections k X s U) (a i))))
  exact hn.symm.trans (congrArg (e.hom.app V) (P.compatible U V hU hV h a))

end
end Common.AlgebraicGeometry.CanonicalModulePresentation
