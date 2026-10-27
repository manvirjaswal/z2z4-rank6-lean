import Common.AlgebraicGeometry.Jacobian
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Rational points of abelian varieties

For an abelian variety over Spec k, its rational points are sections
of its structure morphism. The group operation is induced by its
group-scheme multiplication, using Mathlib's cartesian Hom group. The
additive notation is only the standard Additive wrapper of that group.
-/

namespace AlgebraicGeometry.Jacobian
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
universe u
variable {S : Scheme.{u}}

local instance pointOverCartesian : CartesianMonoidalCategory (Over S) :=
  Over.cartesianMonoidalCategory S
local instance pointOverBraided : BraidedCategory (Over S) := Over.braidedCategory S

/-- Rational sections, with the group law of the group scheme. -/
abbrev AbelianVariety.Points (A : AbelianVariety S) :=
  Additive (𝟙_ (Over S) ⟶ A.group.X)

instance AbelianVariety.pointsAddCommGroup (A : AbelianVariety S) :
    AddCommGroup A.Points := inferInstance

/-- The zero section is the identity in the induced point group. -/
theorem AbelianVariety.points_zero (A : AbelianVariety S) :
    (0 : A.Points).toMul = A.zero := by
  change CategoryTheory.CartesianMonoidalCategory.toUnit (𝟙_ (Over S)) ≫ _ = _
  have h : CategoryTheory.CartesianMonoidalCategory.toUnit (𝟙_ (Over S)) =
      𝟙 (𝟙_ (Over S)) :=
    CategoryTheory.CartesianMonoidalCategory.toUnit_unique _ _
  rw [h,Category.id_comp]
  rfl

/-- A group-scheme isomorphism induces an isomorphism on its sections. -/
def AbelianVariety.pointsEquiv {A B : AbelianVariety S} (e : A.group ≅ B.group) :
    A.Points ≃+ B.Points := by
  let i : A.group.X ≅ B.group.X := (CommGrp.forget (Over S)).mapIso e
  letI : IsMonHom i.hom := e.hom.hom.hom.isMonHom_hom
  exact (CategoryTheory.Hom.mulEquivCongrRight i (𝟙_ (Over S))).toAdditive

end
end AlgebraicGeometry.Jacobian
