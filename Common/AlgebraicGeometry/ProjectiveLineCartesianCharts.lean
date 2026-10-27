import Common.AlgebraicGeometry.ProjectiveLineBaseChangeCharts
import Common.AlgebraicGeometry.PolynomialCoefficientPullback

/-! Cartesian constant-field squares on both P1 charts. -/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory CategoryTheory.Limits Charts
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

def polynomialChartIso (i : Fin 2) :
    Spec (CommRingCat.of (Polynomial k)) ≅ Spec (CommRingCat.of (ChartRing k i)) :=
  Scheme.Spec.mapIso (polynomialEquiv k i).toRingEquiv.toCommRingCatIso.op

theorem chart_field_isPullback (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientHom k K i)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing K i))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k i))))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  apply (PolynomialCoefficientPullback.affineLine_isPullback k K).of_iso
    (polynomialChartIso K i) (polynomialChartIso k i) (Iso.refl _) (Iso.refl _)
  · change Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K)))≫
        Spec.map (CommRingCat.ofHom (polynomialEquiv k i).toRingHom)=
      Spec.map (CommRingCat.ofHom (polynomialEquiv K i).toRingHom)≫
        Spec.map (CommRingCat.ofHom (chartCoefficientHom k K i))
    rw [←Spec.map_comp,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact (chartCoefficientHom_polynomial k K i).symm
  · change Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))≫𝟙 _=
      Spec.map (CommRingCat.ofHom (polynomialEquiv K i).toRingHom)≫
        Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing K i)))
    rw [Category.comp_id,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun a=>((polynomialEquiv K i).commutes a).symm)
  · change Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))≫𝟙 _=
      Spec.map (CommRingCat.ofHom (polynomialEquiv k i).toRingHom)≫
        Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k i)))
    rw [Category.comp_id,←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (fun a=>((polynomialEquiv k i).commutes a).symm)
  · simp

end
end AlgebraicGeometry.ProjectiveLine
