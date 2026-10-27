import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Structure-sheaf cohomology over a field

The unit O-module is restricted along the structure
morphism to the coefficient field. Cohomology is Ext from the constant
coefficient sheaf in the category of sheaves of vector spaces.
This is the standard definition of sheaf cohomology; see Stacks,
Lemma 20.5.1 (tag 0B3A) and Lemma 21.12.4 (tag 03FD).
-/

namespace Common.AlgebraicGeometry.StructureSheafCohomology
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

variable (k : Type) [Field k]

abbrev GlobalRing (X : Scheme.{0}) := ↥(X.presheaf.obj (op (⊤ : X.Opens)))
abbrev Sheaves (X : Scheme.{0}) := Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)

instance hasSheafify (X : Scheme.{0}) :
    HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k) :=
  hasSheafifyEssentiallySmallSite _ _

def scalarMap (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) : k →+* GlobalRing X :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ s.appTop).hom

def structureSheafGlobal (X : Scheme.{0}) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} (GlobalRing X)) :=
  (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op (⊤ : X.Opens))
    (isTerminalTop.op)).obj (SheafOfModules.unit X.ringCatSheaf)

def structureSheaf (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) : Sheaves k X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (scalarMap k X s))).obj (structureSheafGlobal X)

def constant (X : Scheme.{0}) : Sheaves k X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).obj (ModuleCat.of k k)

instance hasExt (X : Scheme.{0}) : HasExt.{0} (Sheaves k X) :=
  hasExt_of_enoughInjectives (Sheaves k X)

/-- Degree-`i` structure-sheaf cohomology. -/
abbrev Cohomology (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) (i : ℕ) :=
  CategoryTheory.Abelian.Ext (constant k X) (structureSheaf k X s) i

instance cohomologyModule (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) (i : ℕ) :
    Module k (Cohomology k X s i) := inferInstance

end
end Common.AlgebraicGeometry.StructureSheafCohomology
