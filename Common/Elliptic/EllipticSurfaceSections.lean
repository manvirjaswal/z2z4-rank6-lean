module

public import Common.Elliptic.SurfaceDescentSources
public import Common.Elliptic.WeierstrassSchemeInfinity

@[expose] public section

/-!
# Separate numbered model and section assertions

Gauthier Leterrier, Some Mordell-Weil lattices and applications to sphere
packings, EPFL thesis 10417 (2024), Remark 1.3.9, printed p. 36 (PDF p. 50).
https://infoscience.epfl.ch/record/307330/files/EPFL_TH10417.pdf

The first bullet gives the smooth projective geometrically irreducible
minimal regular model over a perfect constant field; its following
paragraph retains flatness. The second bullet states the natural
bijection between generic rational points and sections.
The section needed
for existence is deduced from that bijection and the constructed
point (0:1:0).

The source calls this numbered statement a Remark, not a Theorem. Its
references are Schütt–Shioda 2019 Theorem 5.19 and Proposition 5.4,
Ulmer 2014 Proposition 2.1.1, and Silverman Advanced Topics III.3.10.
-/
namespace Common.Elliptic.EllipticSurfaceSections
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SurfaceModel Common.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {W : WeierstrassCurve (RatFunc k)}

abbrev Section (M : RegularModel k W) :=
  {s : Base k ⟶ M.scheme // s≫M.projection=𝟙 (Base k)}

abbrev GenericPoint (W : WeierstrassCurve (RatFunc k)) :=
  {p : FieldBase k ⟶ WeierstrassScheme.scheme W //
    p≫WeierstrassScheme.structureMap W=𝟙 (FieldBase k)}

/-- The restriction of a section through the given generic-fiber iso. -/
def genericRestriction (M : RegularModel k W) (s : Section M) : GenericPoint W :=
  let l := pullback.lift (SurfaceModel.genericBaseMap k≫s.val) (𝟙 (FieldBase k))
    (by simp only [Category.assoc,s.property,Category.comp_id,Category.id_comp])
  ⟨l≫M.genericIso.hom,by
    dsimp only [l]
    rw [Category.assoc,M.genericIso_over,pullback.lift_snd]⟩

/-- Existence/minimality clause of Leterrier Remark 1.3.9 p. 36, C=P1. -/
def LeterrierRemark139Models (k : Type) [Field k] [PerfectField k] : Prop :=
  ∀ W : WeierstrassCurve (RatFunc k),W.IsElliptic →
    Nonempty {M : RegularModel k W // M.IsRelativelyMinimal ∧
      ProjectiveScheme.IsProjective k M.scheme M.structureMap ∧
      Function.Surjective M.projection}

/-- The natural point/section bijection in the second bullet of the same remark. -/
def LeterrierRemark139Sections (k : Type) [Field k] [PerfectField k] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)),W.IsElliptic → ∀ M : RegularModel k W,
    M.IsRelativelyMinimal → ProjectiveScheme.IsProjective k M.scheme M.structureMap →
      Function.Surjective M.projection → Function.Bijective (genericRestriction M)

/-- A section follows from the infinity point and the published bijection. -/
theorem model_with_section (k : Type) [Field k] [PerfectField k]
    (hModels : LeterrierRemark139Models k) (hSections : LeterrierRemark139Sections k) :
    ∀ W : WeierstrassCurve (RatFunc k),W.IsElliptic →
      Nonempty {M : RegularModel k W // M.IsRelativelyMinimal ∧ M.HasSection ∧
        ProjectiveScheme.IsProjective k M.scheme M.structureMap} := by
  intro W hW
  obtain ⟨M,hm,hp,hsurj⟩ := hModels W hW
  obtain ⟨s,_⟩ := (hSections W hW M hm hp hsurj).surjective
    ⟨WeierstrassScheme.Infinity.point W,WeierstrassScheme.Infinity.point_over W⟩
  exact ⟨M,hm,⟨s⟩,hp⟩

end
end Common.Elliptic.EllipticSurfaceSections
