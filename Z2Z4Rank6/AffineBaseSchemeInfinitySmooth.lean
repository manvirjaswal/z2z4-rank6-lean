import Z2Z4Rank6.AffineBaseSchemeSmooth
import Z2Z4Rank6.ProjectiveBaseSchemeInfinityData

/-! Smoothness of the second affine chart of the projective C,
Jaswal Lemma 4.1(a), DOI 10.5281/zenodo.23437117. The equations are
u²=1210z²+15 and v²=1215z²+10. The quotient chart is smooth
of relative dimension 1 over Q by three submersive local presentations. -/
namespace Z2Z4Rank6.AffineBaseSchemeInfinitySmooth
noncomputable section
open scoped Classical
open AlgebraicGeometry
open ProjectiveBaseSchemeCharts

abbrev P := InfinityPolynomialRing
abbrev CoordinateRing := InfinityCoordinateRing
abbrev relation := infinityRelation
abbrev definingIdeal := infinityIdeal
abbrev m := infinityZ
abbrev u := infinityU
abbrev v := infinityV
abbrev minorFactor := infinityMinorFactor
abbrev minorFactors_span_top := infinityMinorFactors_span_top
abbrev columnMap := AffineBaseScheme.columnMap
abbrev columnMap_injective := AffineBaseScheme.columnMap_injective

def prePresentation (i : Fin 3) : Algebra.PreSubmersivePresentation ℚ CoordinateRing (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v:=relation) (columnMap i) (columnMap_injective i)

def minorCoefficient (i : Fin 3) : ℚ := ![4,-4840,4860] i

theorem minorCoefficient_ne_zero (i : Fin 3) : minorCoefficient i≠0 := by
  fin_cases i <;> norm_num [minorCoefficient]

private theorem relation_zero_C : relation 0=
    (MvPolynomial.X 1)^2-MvPolynomial.C (1210:ℚ)*(MvPolynomial.X 0)^2-MvPolynomial.C (15:ℚ) := by
  simp [relation,infinityRelation,map_ofNat]

private theorem relation_one_C : relation 1=
    (MvPolynomial.X 2)^2-MvPolynomial.C (1215:ℚ)*(MvPolynomial.X 0)^2-MvPolynomial.C (10:ℚ) := by
  simp [relation,infinityRelation,map_ofNat]

private theorem pderiv_relation_zero (j : Fin 3) :
    MvPolynomial.pderiv j (relation 0)=
      2*MvPolynomial.X 1*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 1-
        MvPolynomial.C (1210:ℚ)*(2*MvPolynomial.X 0*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 0) := by
  rw [relation_zero_C]
  simp only [map_sub,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Nat.reduceSub,pow_one,sub_zero,Nat.cast_ofNat]

private theorem pderiv_relation_one (j : Fin 3) :
    MvPolynomial.pderiv j (relation 1)=
      2*MvPolynomial.X 2*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 2-
        MvPolynomial.C (1215:ℚ)*(2*MvPolynomial.X 0*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 0) := by
  rw [relation_one_C]
  simp only [map_sub,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Nat.reduceSub,pow_one,sub_zero,Nat.cast_ofNat]

/-- Determinant computation in the quotient algebra. -/
theorem prePresentation_jacobian (i : Fin 3) :
    (prePresentation i).jacobian=algebraMap ℚ CoordinateRing (minorCoefficient i)*minorFactor i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_fin_two]
  simp only [-Matrix.cons_val,Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change Ideal.Quotient.mk definingIdeal
    (MvPolynomial.pderiv (columnMap i 0) (relation 0)*MvPolynomial.pderiv (columnMap i 1) (relation 1)-
      MvPolynomial.pderiv (columnMap i 0) (relation 1)*MvPolynomial.pderiv (columnMap i 1) (relation 0))=
    algebraMap ℚ CoordinateRing (minorCoefficient i)*minorFactor i
  simp only [-Matrix.cons_val,pderiv_relation_zero,pderiv_relation_one]
  fin_cases i <;>
    simp [-Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,columnMap,AffineBaseScheme.columnMap,minorCoefficient,minorFactor,infinityMinorFactor,infinityZ,infinityU,infinityV,map_ofNat] <;> ring

abbrev Chart (i : Fin 3) := Localization.Away (minorFactor i)

def chartPrePresentation (i : Fin 3) :
    Algebra.PreSubmersivePresentation ℚ (Chart i) (Unit⊕Fin 3) (Unit⊕Fin 2) :=
  (Algebra.PreSubmersivePresentation.localizationAway (Chart i) (minorFactor i)).comp
    (prePresentation i)

theorem chartPrePresentation_jacobian_isUnit (i : Fin 3) :
    IsUnit (chartPrePresentation i).jacobian := by
  have hq : IsUnit (algebraMap CoordinateRing (Chart i) (minorFactor i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hc : IsUnit (algebraMap ℚ CoordinateRing (minorCoefficient i)) :=
    (isUnit_iff_ne_zero.mpr (minorCoefficient_ne_zero i)).map (algebraMap ℚ CoordinateRing)
  have hP : IsUnit (algebraMap CoordinateRing (Chart i) (prePresentation i).jacobian) := by
    rw [prePresentation_jacobian,map_mul]
    exact (hc.map (algebraMap CoordinateRing (Chart i))).mul hq
  rw [chartPrePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,Algebra.smul_def]
  exact hP.mul hq

/-- A finite submersive presentation of each localization. -/
def chartPresentation (i : Fin 3) :
    Algebra.SubmersivePresentation ℚ (Chart i) (Unit⊕Fin 3) (Unit⊕Fin 2) where
  __ := chartPrePresentation i
  jacobian_isUnit := chartPrePresentation_jacobian_isUnit i

instance chart_standard_smooth (i : Fin 3) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Chart i) :=
  (chartPresentation i).isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension])

/-- The ring map is locally standard smooth of relative dimension 1. -/
theorem locally_standard_smooth :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ CoordinateRing) := by
  refine ⟨Set.range minorFactor,minorFactors_span_top,?_⟩
  rintro t ⟨i,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap CoordinateRing (Chart i)).comp (algebraMap ℚ CoordinateRing))
  rw [←IsScalarTower.algebraMap_eq ℚ CoordinateRing (Chart i),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact chart_standard_smooth i

/-- The coordinate algebra is smooth over Q in Mathlib's algebraic sense. -/
theorem coordinateRing_smooth : Algebra.Smooth ℚ CoordinateRing := by
  rw [←RingHom.smooth_algebraMap]
  apply RingHom.smooth_iff_locally_isStandardSmooth.mpr
  exact RingHom.locally_of_locally
    (fun h => RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 _ h)
    locally_standard_smooth

/-- Affine scheme smoothness, with relative dimension 1. -/
theorem infinityStructureMap_smooth : SmoothOfRelativeDimension 1 infinityStructureMap := by
  dsimp only [infinityStructureMap,infinityScheme]
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 1)]
  exact locally_standard_smooth

instance : SmoothOfRelativeDimension 1 infinityStructureMap := infinityStructureMap_smooth

end
end Z2Z4Rank6.AffineBaseSchemeInfinitySmooth
