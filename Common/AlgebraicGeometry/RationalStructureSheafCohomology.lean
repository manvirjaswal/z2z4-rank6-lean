module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LeftExact

@[expose] public section

/-!
# Rational structure-sheaf cohomology objects

The structure sheaf is first the unit O-module. Its canonical
global-section scalar action is restricted along the structure
morphism to Spec Q. H1 is Ext1 from the constant rational sheaf
to this rational module sheaf, in the rational sheaf category.

The standard identification with sheaf cohomology is Stacks 20.5.1 (tag 0B3A)
and 21.12.4 (tag 03FD); the generic affine-cover comparison is separate.
-/

namespace AlgebraicGeometry.RationalStructureSheafCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

abbrev Base := Spec (CommRingCat.of ℚ)
abbrev GlobalRing (X : Scheme.{0}) := ↥(X.presheaf.obj (op (⊤ : X.Opens)))
abbrev RationalSheaves (X : Scheme.{0}) :=
  Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)

instance rationalSheafHasSheafify (X : Scheme.{0}) :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  hasSheafifyEssentiallySmallSite _ _

/-- The rational coefficient map induced by the structure morphism. -/
def qToGlobal (X : Scheme.{0}) (s : X⟶Base) : ℚ→+*GlobalRing X :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ s.appTop).hom

/-- The structure sheaf with its canonical global-section module action. -/
def structureSheafGlobal (X : Scheme.{0}) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} (GlobalRing X)) :=
  (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op (⊤ : X.Opens))
    (isTerminalTop.op)).obj (SheafOfModules.unit X.ringCatSheaf)

/-- The rational module structure on O, induced by the map to Spec Q. -/
def structureSheafQ (X : Scheme.{0}) (s : X⟶Base) : RationalSheaves X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (qToGlobal X s))).obj (structureSheafGlobal X)

/-- The constant rational sheaf. -/
def constantQ (X : Scheme.{0}) : RationalSheaves X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

instance rationalSheafHasExt (X : Scheme.{0}) : HasExt.{0} (RationalSheaves X) :=
  hasExt_of_enoughInjectives (RationalSheaves X)

/-- Rational degree-one sheaf cohomology, as Ext in the rational module-sheaf category. -/
abbrev H1 (X : Scheme.{0}) (s : X⟶Base) :=
  CategoryTheory.Abelian.Ext (constantQ X) (structureSheafQ X s) 1

instance h1Module (X : Scheme.{0}) (s : X⟶Base) : Module ℚ (H1 X s) := inferInstance

/-- Sections of O on U with their canonical rational module action. -/
abbrev sectionModule (X : Scheme.{0}) (s : X⟶Base) (U : X.Opens) : ModuleCat ℚ :=
  (structureSheafQ X s).obj.obj (op U)

theorem sectionModule_type (X : Scheme.{0}) (s : X⟶Base) (U : X.Opens) :
    ↥(sectionModule X s U)=↥(X.presheaf.obj (op U)) := rfl

/-- The restriction of structure-sheaf sections, as a rational linear map. -/
def restriction (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens) (h : V≤U) :
    sectionModule X s U→ₗ[ℚ]sectionModule X s V :=
  ((structureSheafQ X s).obj.map (homOfLE h).op).hom

theorem restriction_apply (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens) (h : V≤U)
    (a : sectionModule X s U) :
    restriction X s U V h a=(X.presheaf.map (homOfLE h).op) a := rfl

end
end AlgebraicGeometry.RationalStructureSheafCohomology
