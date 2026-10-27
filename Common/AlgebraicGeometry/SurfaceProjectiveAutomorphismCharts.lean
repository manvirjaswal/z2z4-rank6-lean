module

public import Common.AlgebraicGeometry.ProjValuedPointCharts

@[expose] public section

/-! Evaluation in an arbitrary projective chart whose denominator is a unit. -/
namespace AlgebraicGeometry.ProjUnitChart
noncomputable section
open CategoryTheory HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {R : Type} [CommRing R] (e : A →+* R) (r : A) (he : IsUnit (e r))

def evaluation : Away 𝒜 r →+* R :=
  (Localization.awayLift e r he).comp (algebraMap (Away 𝒜 r) (Localization.Away r))

theorem evaluation_mk_field {L : Type} [Field L] (e : A →+* L) (r : A)
    (he : e r≠0) {d : ℕ} (hr : r∈𝒜 d) (j : ℕ) (p : A) (hp : p∈𝒜 (j • d)) :
    evaluation 𝒜 e r (isUnit_iff_ne_zero.mpr he)
      (Away.mk 𝒜 hr j p hp)=e p/(e r)^j := by
  change Localization.awayLift e r (isUnit_iff_ne_zero.mpr he)
    (Localization.mk p ⟨r^j,j,rfl⟩)=_
  rw [Localization.awayLift_mk e r p (e r)⁻¹ (mul_inv_cancel₀ he) j]
  simp only [div_eq_mul_inv,inv_pow]

variable {X : Scheme} (f : A →+* Γ(X,⊤))
  (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f=⊤)
  {n : ℕ} (hn : 0<n) (hr : r∈𝒜 n) (hfr : IsUnit (f r))

theorem fromGlobalSections_eq_chart :
    Proj.fromOfGlobalSections 𝒜 f hf=
      X.toSpecΓ≫Spec.map (CommRingCat.ofHom (evaluation 𝒜 f r hfr))≫
        Proj.awayι 𝒜 r hr hn := by
  have htop : X.basicOpen (f r)=⊤ := X.basicOpen_of_isUnit hfr
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
          (Localization.awayLift f r hfr) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    simp
  simp only [hfull,RingHom.comp_assoc,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap_assoc]
  simp only [morphismRestrict_ι_assoc,Scheme.isoOfEq_inv_ι_assoc]
  simp only [evaluation,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc]

end
end AlgebraicGeometry.ProjUnitChart

namespace AlgebraicGeometry.ProjValuedPoint
noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {k K A : Type} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
variable (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n) (r : A) (hr : r∈𝒜 n) (he : e r=1)

theorem point_eq_unit_chart (s : A) {d : ℕ} (hs : s∈𝒜 d) (hd : 0<d)
    (hes : IsUnit (e s)) :
    point 𝒜 e hn r hr he=
      Spec.map (CommRingCat.ofHom (ProjUnitChart.evaluation 𝒜 e.toRingHom s hes))≫
        Proj.awayι 𝒜 s hs hd := by
  have hes' : IsUnit (globalEvaluation e s) :=
    hes.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  rw [point,ProjUnitChart.fromGlobalSections_eq_chart 𝒜 s (globalEvaluation e)
    (irrelevant_map_eq_top 𝒜 e hn r hr he) hd hs hes']
  have hfull : Localization.awayLift (globalEvaluation e) s hes'=
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
        (Localization.awayLift e.toRingHom s hes) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp [globalEvaluation]
  have hg : (Source K).toSpecΓ≫
      Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)=𝟙 _ :=
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of K)
  simp only [ProjUnitChart.evaluation,hfull,RingHom.comp_assoc,
    CommRingCat.ofHom_comp,Spec.map_comp,←Category.assoc,
    hg,Category.id_comp]

end
end AlgebraicGeometry.ProjValuedPoint
