import Common.Elliptic.EllipticSurfaceSections

/-!
# Automorphisms from uniqueness of the minimal elliptic model

Gauthier Leterrier, *Some Mordell-Weil lattices and applications to sphere
packings*, EPFL thesis 10417 (2024), Remark 1.3.9, printed p. 36 (PDF p. 50),
first bullet: the smooth projective minimal regular pair with prescribed
elliptic generic fiber is unique up to isomorphism over the base curve.
https://infoscience.epfl.ch/record/307330/files/EPFL_TH10417.pdf

The input below is only this uniqueness clause for C=P1. Reprojection by
a base automorphism and its compatibility with a generic
curve isomorphism are constructed.
-/
namespace Common.AlgebraicGeometry.SurfaceModelAutomorphism
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Common.Elliptic Common.Elliptic.SurfaceModel
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k]
variable {W : WeierstrassCurve (RatFunc k)}

/-- The isomorphism-of-pairs uniqueness clause of Leterrier Remark 1.3.9,
first bullet, p. 36, over the projective line and a perfect constant field. -/
def LeterrierRemark139Uniqueness (k : Type) [Field k] [PerfectField k] : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc k)), W.IsElliptic →
    ∀ (M N : RegularModel k W),
      Function.Surjective M.projection → Function.Surjective N.projection →
      M.IsRelativelyMinimal → N.IsRelativelyMinimal →
      ProjectiveScheme.IsProjective k M.scheme M.structureMap →
      ProjectiveScheme.IsProjective k N.scheme N.structureMap →
        Nonempty {a : M.scheme ≅ N.scheme // a.hom≫N.projection=M.projection}

/-- The section proves surjectivity of the surface projection. -/
theorem projection_surjective_of_section (M : RegularModel k W) (hs : M.HasSection) :
    Function.Surjective M.projection := by
  obtain ⟨s,hs⟩ := hs
  intro x
  refine ⟨s x,?_⟩
  have hx := congrArg (fun f : Base k ⟶ Base k=>f x) hs
  change M.projection (s x)=x at hx
  exact hx

structure CompatibleAutomorphisms (W : WeierstrassCurve (RatFunc k)) where
  base : Base k ≅ Base k
  field : FieldBase k ≅ FieldBase k
  curve : WeierstrassScheme.scheme W ≅ WeierstrassScheme.scheme W
  base_over : base.hom≫ProjectiveLine.structureMap k=ProjectiveLine.structureMap k
  generic_base : field.hom≫SurfaceModel.genericBaseMap k=
    SurfaceModel.genericBaseMap k≫base.hom
  curve_over : curve.hom≫WeierstrassScheme.structureMap W=
    WeierstrassScheme.structureMap W≫field.hom

namespace CompatibleAutomorphisms
variable (a : CompatibleAutomorphisms W)

def symm : CompatibleAutomorphisms W where
  base := a.base.symm
  field := a.field.symm
  curve := a.curve.symm
  base_over := by
    change a.base.inv≫ProjectiveLine.structureMap k=ProjectiveLine.structureMap k
    calc
      _=a.base.inv≫(a.base.hom≫ProjectiveLine.structureMap k) := by rw [a.base_over]
      _=_ := a.base.inv_hom_id_assoc _
  generic_base := by
    change a.field.inv≫SurfaceModel.genericBaseMap k=SurfaceModel.genericBaseMap k≫a.base.inv
    apply (cancel_mono a.base.hom).mp
    rw [Category.assoc,Category.assoc,a.base.inv_hom_id,Category.comp_id,
      ←a.generic_base,a.field.inv_hom_id_assoc]
  curve_over := by
    change a.curve.inv≫WeierstrassScheme.structureMap W=WeierstrassScheme.structureMap W≫a.field.inv
    apply (cancel_mono a.field.hom).mp
    rw [Category.assoc,Category.assoc,a.field.inv_hom_id,Category.comp_id,
      ←a.curve_over,a.curve.inv_hom_id_assoc]

variable (M : RegularModel k W)

def genericPullbackMap : pullback (M.projection≫a.base.hom) (SurfaceModel.genericBaseMap k) ⟶
    pullback M.projection (SurfaceModel.genericBaseMap k) :=
  pullback.map _ _ _ _ (𝟙 M.scheme) a.field.inv a.base.inv
    (by simp) (by exact a.symm.generic_base.symm)

instance genericPullbackMap_isIso : IsIso (a.genericPullbackMap M) := by
  dsimp only [genericPullbackMap]
  infer_instance

def reprojectGenericIso :
    pullback (M.projection≫a.base.hom) (SurfaceModel.genericBaseMap k) ≅
      WeierstrassScheme.scheme W :=
  asIso (a.genericPullbackMap M) ≪≫ M.genericIso ≪≫ a.curve

@[reassoc] theorem reprojectGenericIso_over :
    (a.reprojectGenericIso M).hom≫WeierstrassScheme.structureMap W=
      pullback.snd (M.projection≫a.base.hom) (SurfaceModel.genericBaseMap k) := by
  simp only [reprojectGenericIso,Iso.trans_hom,asIso_hom,Category.assoc,a.curve_over]
  rw [←Category.assoc _ (WeierstrassScheme.structureMap W),M.genericIso_over]
  simp [genericPullbackMap]

/-- The same total space, with its projection composed with the base
isomorphism. The generic fiber is reidentified by the proved maps. -/
def reproject : RegularModel k W where
  scheme := M.scheme
  projection := M.projection≫a.base.hom
  proper := by infer_instance
  flat := by infer_instance
  regular := M.regular
  smooth := by simpa only [Category.assoc,a.base_over] using M.smooth
  geometricallyIntegral := by
    simpa only [Category.assoc,a.base_over] using M.geometricallyIntegral
  dimension := M.dimension
  genericIso := a.reprojectGenericIso M
  genericIso_over := a.reprojectGenericIso_over M

theorem reproject_structureMap : (a.reproject M).structureMap=M.structureMap := by
  change (M.projection≫a.base.hom)≫ProjectiveLine.structureMap k=_
  rw [Category.assoc,a.base_over]
  rfl

@[reassoc] theorem reproject_genericInclusion :
    (a.reproject M).genericInclusion=a.curve.inv≫M.genericInclusion := by
  have hm : a.genericPullbackMap M≫pullback.fst M.projection (SurfaceModel.genericBaseMap k)=
      pullback.fst (M.projection≫a.base.hom) (SurfaceModel.genericBaseMap k) := by
    simp [genericPullbackMap]
  have hi : (asIso (a.genericPullbackMap M)).inv≫
      pullback.fst (M.projection≫a.base.hom) (SurfaceModel.genericBaseMap k)=
        pullback.fst M.projection (SurfaceModel.genericBaseMap k) := by
    rw [←hm,←Category.assoc]
    exact (asIso (a.genericPullbackMap M)).inv_hom_id_assoc _
  simp only [RegularModel.genericInclusion,reproject,reprojectGenericIso,Iso.trans_inv,
    Category.assoc,hi]

theorem reproject_hasSection (hs : M.HasSection) : (a.reproject M).HasSection := by
  obtain ⟨s,hs⟩ := hs
  refine ⟨⟨a.base.inv≫s,?_⟩⟩
  change (a.base.inv≫s)≫(M.projection≫a.base.hom)=𝟙 _
  rw [Category.assoc,←Category.assoc s,hs,Category.id_comp,a.base.inv_hom_id]

theorem reproject_minimal (hm : M.IsRelativelyMinimal) : (a.reproject M).IsRelativelyMinimal := by
  intro N f
  let N' := a.symm.reproject N
  let f' : RegularModel.Hom M N' := {
    hom := f.hom
    over_base := by
      change f.hom≫(N.projection≫a.base.inv)=M.projection
      rw [←Category.assoc,f.over_base]
      change (M.projection≫a.base.hom)≫a.base.inv=M.projection
      simp
    generic := by
      change M.genericInclusion≫f.hom=(a.symm.reproject N).genericInclusion
      rw [a.symm.reproject_genericInclusion]
      change M.genericInclusion≫f.hom=a.curve.hom≫N.genericInclusion
      rw [←f.generic,a.reproject_genericInclusion,←Category.assoc,←Category.assoc,
        a.curve.hom_inv_id,Category.id_comp] }
  exact hm N' f'

theorem reproject_projective
    (hp : ProjectiveScheme.IsProjective k M.scheme M.structureMap) :
    ProjectiveScheme.IsProjective k (a.reproject M).scheme (a.reproject M).structureMap := by
  rw [a.reproject_structureMap]
  exact hp

end CompatibleAutomorphisms

/-- Published uniqueness yields a surface automorphism over the
base automorphism once its generic compatibility has been proved. -/
theorem automorphism_of_unique_model [PerfectField k]
    (hUnique : LeterrierRemark139Uniqueness k) (hW : W.IsElliptic)
    (M : RegularModel k W) (hm : M.IsRelativelyMinimal) (hs : M.HasSection)
    (hp : ProjectiveScheme.IsProjective k M.scheme M.structureMap)
    (a : CompatibleAutomorphisms W) :
    ∃ f : M.scheme ≅ M.scheme, f.hom≫M.projection=M.projection≫a.base.hom := by
  obtain ⟨f,hf⟩ := hUnique W hW (a.reproject M) M
    (projection_surjective_of_section _ (a.reproject_hasSection M hs))
    (projection_surjective_of_section M hs)
    (a.reproject_minimal M hm) hm (a.reproject_projective M hp) hp
  exact ⟨f,hf⟩

end
end Common.AlgebraicGeometry.SurfaceModelAutomorphism
