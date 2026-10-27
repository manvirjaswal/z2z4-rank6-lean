module

public import Common.AlgebraicGeometry.ModuleSheafCohomology
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

@[expose] public section

/-!
# Higher direct images of O-modules

The functor is the right-derived functor of the scheme
module-sheaf pushforward. Its input for R^i f_*O is the unit
module. No cohomology group is replaced by a prescribed vector space.
-/
namespace Common.AlgebraicGeometry.HigherDirectImage
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def module (M : X.Modules) (i : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived i).obj M

def structureSheaf (i : ℕ) : Y.Modules :=
  module f (SheafOfModules.unit X.ringCatSheaf) i

end
end Common.AlgebraicGeometry.HigherDirectImage
