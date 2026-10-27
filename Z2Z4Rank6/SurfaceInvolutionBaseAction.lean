module

public import Z2Z4Rank6.SurfaceInvolutionBase
public import Common.AlgebraicGeometry.SurfaceProjectiveAutomorphismCharts

@[expose] public section

/-! Exact compatibility of the projective involution with n ↦ 9801/n. -/
namespace Z2Z4Rank6.SurfaceInvolution
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open ProjectiveLine.Charts
set_option backward.isDefEq.respectTransparency false
local instance rationalFunctionAlgebraAction : Algebra ℚ F := RatFunc.instAlgebraOfPolynomial ℚ ℚ

def baseGenericEvaluation : BaseRing →ₐ[ℚ] F := MvPolynomial.aeval ![RatFunc.X,1]
def transformedDenominator : BaseRing := baseGraded (ProjectiveLine.coordinate ℚ 1)

theorem transformedDenominator_degree :
    transformedDenominator∈ProjectiveLine.grading ℚ 1 :=
  baseGraded.map_mem (ProjectiveLine.coordinate_degree ℚ 1)

theorem transformedDenominator_evaluation :
    baseGenericEvaluation transformedDenominator=(RatFunc.X : F)/99 := by
  simp [baseGenericEvaluation,transformedDenominator,baseGraded,baseSubstitution,
    ProjectiveLine.coordinate]
  ring

theorem transformedDenominator_ne_zero : baseGenericEvaluation transformedDenominator≠0 := by
  rw [transformedDenominator_evaluation]
  exact div_ne_zero RatFunc.X_ne_zero (by norm_num)

def transformedChartEvaluation : ChartRing ℚ 1 →ₐ[ℚ] F :=
  ((ProjUnitChart.evaluation (ProjectiveLine.grading ℚ) baseGenericEvaluation.toRingHom
    transformedDenominator (isUnit_iff_ne_zero.mpr transformedDenominator_ne_zero)).comp
      (Away.map baseGraded (ProjectiveLine.coordinate ℚ 1))).toRatAlgHom

theorem transformedChartEvaluation_ratio (j : Fin 2) :
    transformedChartEvaluation (ProjectiveLine.Charts.ratio ℚ 1 j)=
      (MvPolynomial.aeval ![9801/(RatFunc.X : F),1]) (ProjectiveLine.coordinate ℚ j) := by
  change ProjUnitChart.evaluation (ProjectiveLine.grading ℚ) baseGenericEvaluation.toRingHom
      transformedDenominator (isUnit_iff_ne_zero.mpr transformedDenominator_ne_zero)
    (Away.map baseGraded (ProjectiveLine.coordinate ℚ 1)
      (Away.mk (ProjectiveLine.grading ℚ) (ProjectiveLine.coordinate_degree ℚ 1)
        1 (ProjectiveLine.coordinate ℚ j) (by simpa using ProjectiveLine.coordinate_degree ℚ j)))=_
  rw [Away.map_mk]
  rw [ProjUnitChart.evaluation_mk_field _ _ _ transformedDenominator_ne_zero]
  change baseGenericEvaluation (baseGraded (ProjectiveLine.coordinate ℚ j)) /
    (baseGenericEvaluation transformedDenominator)^1=_
  rw [transformedDenominator_evaluation]
  fin_cases j <;> simp [baseGenericEvaluation,baseGraded,baseSubstitution,ProjectiveLine.coordinate]
  all_goals field_simp [RatFunc.X_ne_zero]
  all_goals ring

theorem transformedChartEvaluation_eq : transformedChartEvaluation=
    chartEvaluation 1 (MvPolynomial.aeval ![9801/(RatFunc.X : F),1])
      (by simp [ProjectiveLine.coordinate]) := by
  apply chartAlgHom_ext ℚ 1
  intro j
  rw [transformedChartEvaluation_ratio,chartEvaluation_ratio]

theorem genericPoint_baseInvolution :
    ProjectiveLine.genericPoint ℚ≫baseInvolution.hom=
      ProjectiveLine.affinePoint ℚ F (9801/(RatFunc.X : F)) := by
  have hg : ProjectiveLine.genericPoint ℚ=
      Spec.map (CommRingCat.ofHom (ProjUnitChart.evaluation (ProjectiveLine.grading ℚ)
        baseGenericEvaluation.toRingHom transformedDenominator
          (isUnit_iff_ne_zero.mpr transformedDenominator_ne_zero)))≫
        Proj.awayι (ProjectiveLine.grading ℚ) transformedDenominator
          transformedDenominator_degree (by decide : 0<1) := by
    exact ProjValuedPoint.point_eq_unit_chart (ProjectiveLine.grading ℚ)
      baseGenericEvaluation (by decide : 0<1)
      (ProjectiveLine.coordinate ℚ 1) (ProjectiveLine.coordinate_degree ℚ 1)
      (by simp [baseGenericEvaluation,ProjectiveLine.coordinate]) transformedDenominator
      transformedDenominator_degree (by decide : 0<1)
      (isUnit_iff_ne_zero.mpr transformedDenominator_ne_zero)
  rw [hg,Category.assoc]
  change _≫(Proj.awayι _ _ _ _≫Proj.map baseGraded _)=_
  unfold transformedDenominator
  rw [Proj.awayι_comp_map baseGraded _ (by decide : 0<1)
    (ProjectiveLine.coordinate ℚ 1) (ProjectiveLine.coordinate_degree ℚ 1)]
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom transformedChartEvaluation.toRingHom)≫
    chartInclusion ℚ 1=_
  rw [transformedChartEvaluation_eq,ProjectiveLine.affinePoint_eq_chart]

theorem genericBaseInvolution_over :
    genericBaseInvolution.hom≫ProjectiveLine.genericPoint ℚ=
      ProjectiveLine.genericPoint ℚ≫baseInvolution.hom := by
  rw [genericPoint_baseInvolution]
  change Spec.map (CommRingCat.ofHom reciprocalFieldMap.toRingHom)≫
    ProjectiveLine.affinePoint ℚ F RatFunc.X=_
  rw [ProjectiveLine.affinePoint_sourceMap ℚ reciprocalFieldMap,reciprocalFieldMap_X]

end
end Z2Z4Rank6.SurfaceInvolution
