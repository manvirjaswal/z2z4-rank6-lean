import Common.AlgebraicGeometry.AbelianVarietyPoints

/-!
# Translations on abelian varieties

Translations are over-base scheme isomorphisms obtained from the
commutative group object. Their inverse identities are formal
consequences of the group-object diagrams.
-/

namespace AlgebraicGeometry.Jacobian
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.MonObj
universe u
variable {S : Scheme.{u}}

local instance translationOverCartesian : CartesianMonoidalCategory (Over S) :=
  Over.cartesianMonoidalCategory S
local instance translationOverBraided : BraidedCategory (Over S) := Over.braidedCategory S

def AbelianVariety.translate (A : AbelianVariety S) (b : 𝟙_ (Over S) ⟶ A.group.X) :
    A.group.X ⟶ A.group.X :=
  (toUnit A.group.X ≫ b) * 𝟙 A.group.X

theorem AbelianVariety.translate_comp (A : AbelianVariety S)
    (b c : 𝟙_ (Over S) ⟶ A.group.X) :
    A.translate b ≫ A.translate c = A.translate (c*b) := by
  simp only [AbelianVariety.translate,MonObj.comp_mul,Category.comp_id]
  have hu : (toUnit A.group.X ≫ b * 𝟙 A.group.X) ≫ toUnit A.group.X = toUnit A.group.X :=
    toUnit_unique _ _
  rw [←Category.assoc,hu]
  exact (mul_assoc _ _ _).symm

theorem AbelianVariety.translate_one (A : AbelianVariety S) : A.translate 1 = 𝟙 A.group.X := by
  simp [AbelianVariety.translate,MonObj.comp_one]

def AbelianVariety.translationIso (A : AbelianVariety S)
    (b : 𝟙_ (Over S) ⟶ A.group.X) : A.group.X ≅ A.group.X where
  hom := A.translate b
  inv := A.translate b⁻¹
  hom_inv_id := by rw [A.translate_comp,inv_mul_cancel,A.translate_one]
  inv_hom_id := by rw [A.translate_comp,mul_inv_cancel,A.translate_one]

theorem AbelianVariety.point_translate (A : AbelianVariety S)
    (p b : 𝟙_ (Over S) ⟶ A.group.X) : p ≫ A.translate b = b*p := by
  simp only [AbelianVariety.translate,MonObj.comp_mul,Category.comp_id]
  have hu : p ≫ toUnit A.group.X = 𝟙 (𝟙_ (Over S)) := toUnit_unique _ _
  rw [←Category.assoc,hu,Category.id_comp]

end
end AlgebraicGeometry.Jacobian
