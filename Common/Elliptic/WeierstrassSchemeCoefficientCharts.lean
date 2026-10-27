import Common.Elliptic.WeierstrassSchemeCoefficientMap
import Common.Elliptic.WeierstrassSchemeChartEvaluation
import Mathlib.AlgebraicGeometry.Pullbacks

/-! Coefficient maps on the homogeneous localization charts. -/
namespace WeierstrassScheme.CoefficientMap
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization GenericCharts
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] (f : k →+* K)
variable (W : WeierstrassCurve k)

def chartHom (i : Fin 3) : ChartRing W i →+* ChartRing (W.map f) i :=
  Proj.chartRingHom (gradedHom f W) (coordinate W i) (coordinate (W.map f) i)
    (gradedHom_coordinate f W i)

@[simp] theorem chartHom_ratio (i j : Fin 3) :
    chartHom f W i (ratio W i j)=ratio (W.map f) i j := by
  rw [chartHom,ratio,Proj.chartRingHom_mk]
  simp only [gradedHom_coordinate]
  rfl

@[simp] theorem chartHom_scalar (i : Fin 3) (a : k) :
    chartHom f W i (algebraMap k (ChartRing W i) a)=
      algebraMap K (ChartRing (W.map f) i) (f a) := by
  change Proj.chartRingHom (gradedHom f W) (coordinate W i) (coordinate (W.map f) i)
    (gradedHom_coordinate f W i)
      (fromZeroRingHom (grading W) (Submonoid.powers (coordinate W i))
        (algebraMap k (grading W 0) a))=_
  rw [Proj.chartRingHom_fromZero]
  change fromZeroRingHom (grading (W.map f)) (Submonoid.powers (coordinate (W.map f) i))
      ((gradedHom f W).gradedZeroRingHom (algebraMap k (grading W 0) a))=
    fromZeroRingHom (grading (W.map f)) (Submonoid.powers (coordinate (W.map f) i))
      (algebraMap K (grading (W.map f) 0) (f a))
  congr 1
  apply Subtype.ext
  exact gradedHom_scalar f W a

theorem chartInclusion_schemeHom (i : Fin 3) :
    chartInclusion (W.map f) i≫schemeHom f W=
      Spec.map (CommRingCat.ofHom (chartHom f W i))≫chartInclusion W i :=
  Proj.chartRingHom_awayι (gradedHom f W) (irrelevant_le f W)
    (coordinate W i) (coordinate (W.map f) i) (gradedHom_coordinate f W i)
      (coordinate_degree W i) (coordinate_degree (W.map f) i) (by decide : 0<1)

theorem chart_isPullback (i : Fin 3) :
    CategoryTheory.IsPullback (Spec.map (CommRingCat.ofHom (chartHom f W i)))
      (chartInclusion (W.map f) i) (chartInclusion W i) (schemeHom f W) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (chartInclusion_schemeHom f W i)
  rw [chartInclusion_opensRange,chartInclusion_opensRange]
  change Proj.map (gradedHom f W) (irrelevant_le f W) ⁻¹ᵁ
    Proj.basicOpen (grading W) (coordinate W i)=_
  rw [Proj.map_preimage_basicOpen,gradedHom_coordinate]

end
end WeierstrassScheme.CoefficientMap
