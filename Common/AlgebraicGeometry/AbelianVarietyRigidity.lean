module

public import Common.AlgebraicGeometry.AbelianVarietyTranslations
public import Common.AlgebraicGeometry.RationalStructureSheafCohomology

@[expose] public section

/-!
# Scheme isomorphisms of abelian varieties give group isomorphisms

Source: J. S. Milne, Abelian Varieties, Arithmetic Geometry
(1986), Corollary 2.2; corrected author reprint 2 January 2022, p. 3,
https://www.jmilne.org/math/xnotes/AVs.pdf. The hypothesis states the source
exactly: every morphism of abelian varieties is a homomorphism followed by
a translation.
-/

namespace AlgebraicGeometry.Jacobian
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open RationalStructureSheafCohomology

local instance rigidityOverCartesian : CartesianMonoidalCategory (Over Base) :=
  Over.cartesianMonoidalCategory Base
local instance rigidityOverBraided : BraidedCategory (Over Base) := Over.braidedCategory Base

/-- Milne Corollary 2.2, restricted only to the rational base field. -/
def MilneCorollary22 : Prop :=
  ∀ (A B : AbelianVariety Base) (f : A.group.X ⟶ B.group.X),
    ∃ (g : A.group ⟶ B.group) (b : 𝟙_ (Over Base) ⟶ B.group.X),
      f = AbelianVariety.homMap g ≫ B.translate b

theorem exists_groupIsoOfSchemeIso (hRigidity : MilneCorollary22)
    (A B : AbelianVariety Base) (e : A.group.X ≅ B.group.X) :
    Nonempty (A.group ≅ B.group) := by
  obtain ⟨g,b,hg⟩ := hRigidity A B e.hom
  have hf : AbelianVariety.homMap g = e.hom ≫ (B.translationIso b).inv := by
    rw [hg,Category.assoc]
    change _ = AbelianVariety.homMap g ≫
      ((B.translationIso b).hom ≫ (B.translationIso b).inv)
    rw [Iso.hom_inv_id,Category.comp_id]
  have hIso : IsIso (AbelianVariety.homMap g) := by
    rw [hf]
    infer_instance
  let : IsIso (AbelianVariety.homMap g) := hIso
  let : IsMonHom (AbelianVariety.homMap g) := g.hom.hom.isMonHom_hom
  exact ⟨CommGrp.mkIso' (asIso (AbelianVariety.homMap g))⟩

def groupIsoOfSchemeIso (hRigidity : MilneCorollary22)
    (A B : AbelianVariety Base) (e : A.group.X ≅ B.group.X) : A.group ≅ B.group :=
  Classical.choice (exists_groupIsoOfSchemeIso hRigidity A B e)

end
end AlgebraicGeometry.Jacobian
