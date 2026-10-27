module

public import Common.AlgebraicGeometry.ProjNormalizedChart

@[expose] public section

/-! The normalized Proj point is its normalized affine-chart point. -/
namespace AlgebraicGeometry.ProjValuedPoint
noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {k K A : Type} [Field k] [Field K] [Algebra k K] [CommRing A] [Algebra k A]
variable (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
variable (e : A →ₐ[k] K) {n : ℕ} (hn : 0<n) (r : A) (hr : r∈𝒜 n) (he : e r=1)

theorem point_eq_chart : point 𝒜 e hn r hr he=
    Spec.map (CommRingCat.ofHom (ProjNormalizedChart.chartEvaluation 𝒜 e.toRingHom r he))≫
      Proj.awayι 𝒜 r hr hn := by
  have he' : globalEvaluation e r=1 := by simp [globalEvaluation,he]
  rw [point,ProjNormalizedChart.fromGlobalSections_eq_chart 𝒜 r (globalEvaluation e)
    (irrelevant_map_eq_top 𝒜 e hn r hr he) hn hr he']
  have hfull : Localization.awayLift (globalEvaluation e) r
      (ProjNormalizedChart.coordinateUnit (globalEvaluation e) r he')=
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
        (Localization.awayLift e.toRingHom r
          (ProjNormalizedChart.coordinateUnit e.toRingHom r he)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext a
    simp [globalEvaluation]
  have hg : (Source K).toSpecΓ≫
      Spec.map (CommRingCat.ofHom (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)=𝟙 _ :=
    toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of K)
  simp only [ProjNormalizedChart.chartEvaluation,hfull,RingHom.comp_assoc,
    CommRingCat.ofHom_comp,Spec.map_comp,←Category.assoc,
    hg,Category.id_comp]

end
end AlgebraicGeometry.ProjValuedPoint
