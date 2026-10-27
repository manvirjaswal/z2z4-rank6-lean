module

public import Common.AlgebraicGeometry.StructureSheafCohomology

@[expose] public section

/-!
# Cohomology of O-modules over a field

An O_X-module is restricted to its coefficient field and
its cohomology is Ext from the constant coefficient sheaf. For the unit
O-module this is definitionally the structure-sheaf cohomology already
used for genus and K3.

References: Stacks Lemma 20.5.1 (tag 0B3A), Lemma 21.12.4 (tag 03FD).
-/
namespace Common.AlgebraicGeometry.ModuleSheafCohomology
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open StructureSheafCohomology
variable (k : Type) [Field k]
variable (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))

def moduleSheafGlobal (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} (GlobalRing X)) :=
  (SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op (⊤ : X.Opens))
    (isTerminalTop.op)).obj M

def coefficientSheaf (M : X.Modules) : Sheaves k X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (ModuleCat.restrictScalars (scalarMap k X s))).obj (moduleSheafGlobal X M)

abbrev Cohomology (M : X.Modules) (i : ℕ) :=
  CategoryTheory.Abelian.Ext (constant k X) (coefficientSheaf k X s M) i

instance cohomologyModule (M : X.Modules) (i : ℕ) : Module k (Cohomology k X s M i) :=
  inferInstance

def euler01 (M : X.Modules) : ℤ :=
  (Module.finrank k (Cohomology k X s M 0) : ℤ)-
    (Module.finrank k (Cohomology k X s M 1) : ℤ)

def HasFiniteCohomology01 (M : X.Modules) : Prop :=
  FiniteDimensional k (Cohomology k X s M 0) ∧ FiniteDimensional k (Cohomology k X s M 1)

theorem unit_cohomology (i : ℕ) :
    Cohomology k X s (SheafOfModules.unit X.ringCatSheaf) i=
      StructureSheafCohomology.Cohomology k X s i := rfl

end
end Common.AlgebraicGeometry.ModuleSheafCohomology
