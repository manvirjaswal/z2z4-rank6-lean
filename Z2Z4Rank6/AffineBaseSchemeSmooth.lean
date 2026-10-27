module

public import Z2Z4Rank6.AffineBaseSchemeJacobian

@[expose] public section

/-!
# Scheme smoothness of the affine base C

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a) and
Theorem 1.2(a), affine part. The three Jacobian localizations have
Mathlib submersive presentations with 4 variables and 3 relations, hence
relative dimension 1. Their proved unit ideal cover gives the
AlgebraicGeometry.SmoothOfRelativeDimension predicate for Spec of the
coordinate quotient.
-/
namespace Z2Z4Rank6.AffineBaseScheme
noncomputable section
open scoped Classical
open AlgebraicGeometry

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
theorem structureMap_smooth : SmoothOfRelativeDimension 1 structureMap := by
  dsimp only [structureMap,scheme]
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 1)]
  exact locally_standard_smooth

instance : SmoothOfRelativeDimension 1 structureMap := structureMap_smooth

end
end Z2Z4Rank6.AffineBaseScheme
