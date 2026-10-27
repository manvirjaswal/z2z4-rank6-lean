import Z2Z4Rank6.AffineBaseFunctionFieldIsoNormalForm
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.Module

/-! Localizing the affine coordinate ring at m gives a free
four-dimensional module over Q[M,M⁻¹], with the 1,u,v,uv basis. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section
abbrev Laurent := LaurentPolynomial ℚ
abbrev overlapDenominators := Algebra.algebraMapSubmonoid CoordinateRing
  (Submonoid.powers (Polynomial.X:Poly))
abbrev OverlapRing := Localization overlapDenominators

instance affineOverlapLaurentAlgebra : Algebra Laurent OverlapRing :=
  localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing) (Submonoid.powers (Polynomial.X:Poly)) CoordinateRing
instance affineOverlapPolyLaurentTower : IsScalarTower Poly Laurent OverlapRing :=
  isScalarTower_localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing)
    (Submonoid.powers (Polynomial.X:Poly)) CoordinateRing
instance affineOverlapRatLaurentTower : IsScalarTower ℚ Laurent OverlapRing :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

def overlapBasis : Module.Basis (Fin 4) Laurent OverlapRing :=
  coordinateBasis.localizationLocalization Laurent
    (Submonoid.powers (Polynomial.X:Poly)) OverlapRing

@[simp] theorem overlapBasis_apply (i : Fin 4) :
    overlapBasis i=algebraMap CoordinateRing OverlapRing (coordinateBasis i) :=
  Module.Basis.localizationLocalization_apply _ _ _ _ i

def overlapCoordinates : OverlapRing ≃ₗ[ℚ] (Fin 4→Laurent) :=
  (overlapBasis.repr.trans (Finsupp.linearEquivFunOnFinite Laurent Laurent (Fin 4))).restrictScalars ℚ

/-- Affine chart restriction, viewed as a Q-linear map. -/
def affineRestriction : CoordinateRing→ₗ[ℚ]OverlapRing :=
  (IsScalarTower.toAlgHom ℚ CoordinateRing OverlapRing).toLinearMap
@[simp] theorem affineRestriction_apply (c : CoordinateRing) :
    affineRestriction c=algebraMap CoordinateRing OverlapRing c := rfl

theorem overlapCoordinates_algebraMap (c : CoordinateRing) (i : Fin 4) :
    overlapCoordinates (algebraMap CoordinateRing OverlapRing c) i=
      Polynomial.toLaurent (coordinateBasis.repr c i) := by
  change overlapBasis.repr (algebraMap CoordinateRing OverlapRing c) i=_
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ c i

@[simp] theorem overlapBasis_zero : overlapBasis 0=1 := by rw [overlapBasis_apply,coordinateBasis_zero,map_one]
@[simp] theorem overlapBasis_one : overlapBasis 1=algebraMap CoordinateRing OverlapRing AffineBaseScheme.u := by
  rw [overlapBasis_apply,coordinateBasis_one]
@[simp] theorem overlapBasis_two : overlapBasis 2=algebraMap CoordinateRing OverlapRing AffineBaseScheme.v := by
  rw [overlapBasis_apply,coordinateBasis_two]
@[simp] theorem overlapBasis_three : overlapBasis 3=
    algebraMap CoordinateRing OverlapRing (AffineBaseScheme.u*AffineBaseScheme.v) := by
  rw [overlapBasis_apply,coordinateBasis_three]
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
