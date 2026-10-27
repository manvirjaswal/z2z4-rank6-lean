module

public import Common.AlgebraicGeometry.ProjValuedPoint
public import Common.AlgebraicGeometry.ProjGradedChartMap

@[expose] public section

/-! Normalized global-section points equal their chart evaluations. -/
namespace AlgebraicGeometry.ProjNormalizedChart
noncomputable section
open CategoryTheory HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {R : Type u} [CommRing R] (e : A →+* R) (r : A) (he : e r=1)

theorem coordinateUnit (h : e r=1) : IsUnit (e r) := h ▸ isUnit_one

def chartEvaluation : Away 𝒜 r →+* R :=
  (Localization.awayLift e r (coordinateUnit e r he)).comp
    (algebraMap (Away 𝒜 r) (Localization.Away r))

variable {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
  (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f=⊤)
  {n : ℕ} (hn : 0<n) (hr : r∈𝒜 n) (hfr : f r=1)

theorem fromGlobalSections_eq_chart :
    Proj.fromOfGlobalSections 𝒜 f hf=
      X.toSpecΓ≫Spec.map (CommRingCat.ofHom (chartEvaluation 𝒜 f r hfr))≫
        Proj.awayι 𝒜 r hr hn := by
  have htop : X.basicOpen (f r)=⊤ := by rw [hfr,Scheme.basicOpen_one]
  have : IsIso (X.basicOpen (f r)).ι := by
    rw [htop]
    change IsIso X.topIso.hom
    infer_instance
  apply (cancel_epi (X.basicOpen (f r)).ι).mp
  rw [←Scheme.Hom.resLE_comp_ι _
      (Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hn hr).ge,
    Proj.fromOfGlobalSections_resLE 𝒜 f hf hn hr]
  simp only [Proj.toBasicOpenOfGlobalSections,Category.assoc,
    Proj.basicOpenIsoSpec_inv_ι]
  have hfull (h : Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f) :
      IsLocalization.map (Localization.Away (f r)) f h=
        (algebraMap Γ(X,⊤) (Localization.Away (f r))).comp
          (Localization.awayLift f r (coordinateUnit f r hfr)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    simp
  simp only [hfull,RingHom.comp_assoc,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap_assoc]
  simp only [morphismRestrict_ι_assoc,Scheme.isoOfEq_inv_ι_assoc]
  simp only [chartEvaluation,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

end
end AlgebraicGeometry.ProjNormalizedChart
