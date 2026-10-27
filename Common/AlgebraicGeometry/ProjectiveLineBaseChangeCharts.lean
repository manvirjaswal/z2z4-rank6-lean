module

public import Common.AlgebraicGeometry.ProjectiveLineBaseChange
public import Common.AlgebraicGeometry.ProjectiveLineChartEquivalence
public import Common.AlgebraicGeometry.ProjGradedChartMap

@[expose] public section

/-! Coefficient maps on both polynomial charts of P1. -/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial Charts HomogeneousLocalization
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

@[simp] theorem coefficientHom_coordinate (i : Fin 2) :
    coefficientHom k K (coordinate k i)=coordinate K i := by
  simp [coefficientHom,coordinate]

def chartCoefficientHom (i : Fin 2) : ChartRing k i →+* ChartRing K i :=
  Proj.chartRingHom (coefficientHom k K) (coordinate k i) (coordinate K i)
    (coefficientHom_coordinate k K i)

@[simp] theorem chartCoefficientHom_ratio (i j : Fin 2) :
    chartCoefficientHom k K i (ratio k i j)=ratio K i j := by
  rw [chartCoefficientHom,ratio,Proj.chartRingHom_mk]
  simp only [coefficientHom_coordinate]
  rfl

@[simp] theorem chartCoefficientHom_scalar (i : Fin 2) (a : k) :
    chartCoefficientHom k K i (algebraMap k (ChartRing k i) a)=
      algebraMap K (ChartRing K i) (algebraMap k K a) := by
  change Proj.chartRingHom (coefficientHom k K) (coordinate k i) (coordinate K i)
    (coefficientHom_coordinate k K i)
      (fromZeroRingHom (grading k) (Submonoid.powers (coordinate k i))
        (algebraMap k (grading k 0) a))=_
  rw [Proj.chartRingHom_fromZero]
  change fromZeroRingHom (grading K) (Submonoid.powers (coordinate K i))
      ((coefficientHom k K).gradedZeroRingHom (algebraMap k (grading k 0) a))=
    fromZeroRingHom (grading K) (Submonoid.powers (coordinate K i))
      (algebraMap K (grading K 0) (algebraMap k K a))
  congr 1
  apply Subtype.ext
  simp [coefficientHom]

theorem chartCoefficientHom_polynomial (i : Fin 2) :
    (polynomialEquiv K i).toRingHom.comp (chartCoefficientHom k K i)=
      (Polynomial.mapRingHom (algebraMap k K)).comp (polynomialEquiv k i).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := (polynomialEquiv k i).symm.surjective x
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | monomial n a =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow]
    fin_cases i <;> simp [polynomialEquiv,fromPolynomial,otherCoordinate]

theorem chartInclusion_coefficientMap (i : Fin 2) :
    chartInclusion K i≫coefficientMap k K=
      Spec.map (CommRingCat.ofHom (chartCoefficientHom k K i))≫chartInclusion k i :=
  Proj.chartRingHom_awayι (coefficientHom k K) (irrelevant_le_coefficientHom k K)
    (coordinate k i) (coordinate K i) (coefficientHom_coordinate k K i)
      (coordinate_degree k i) (coordinate_degree K i) (by decide : 0<1)

theorem chart_isPullback (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartCoefficientHom k K i)))
      (chartInclusion K i) (chartInclusion k i) (coefficientMap k K) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (chartInclusion_coefficientMap k K i)
  rw [chartInclusion_opensRange,chartInclusion_opensRange]
  change Proj.map (coefficientHom k K) (irrelevant_le_coefficientHom k K) ⁻¹ᵁ
    Proj.basicOpen (grading k) (coordinate k i)=_
  rw [Proj.map_preimage_basicOpen,coefficientHom_coordinate]

end
end AlgebraicGeometry.ProjectiveLine
