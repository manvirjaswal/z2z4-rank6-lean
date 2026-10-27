import Z2Z4Rank6.ThirdTwistCoverNormalForm
import Z2Z4Rank6.ThirdTwistCoverLaurent
import Mathlib.RingTheory.Localization.Module

/-! The third-twist base affine overlap, obtained by inverting m,
and its free eight-coefficient Laurent coordinates. -/
namespace Z2Z4Rank6.ThirdTwistCoverOverlap
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev Laurent := LaurentPolynomial ℚ
abbrev AffineRing := ThirdTwistCoverAffine.CoordinateRing
abbrev InfinityRing := ThirdTwistCoverInfinity.CoordinateRing
abbrev affineBasis  := ThirdTwistCoverAffine.basis
abbrev infinityBasis  := ThirdTwistCoverInfinity.basis
abbrev overlapDenominators  := Algebra.algebraMapSubmonoid (AffineRing)
  (Submonoid.powers (Polynomial.X:Poly))
abbrev OverlapRing  := Localization (overlapDenominators)

instance overlapLaurentAlgebra  : Algebra Laurent (OverlapRing) :=
  localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing)
    (Submonoid.powers (Polynomial.X:Poly)) (AffineRing)
instance overlapPolyLaurentTower  : IsScalarTower Poly Laurent (OverlapRing) :=
  isScalarTower_localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing)
    (Submonoid.powers (Polynomial.X:Poly)) (AffineRing)
instance overlapRatLaurentTower  : IsScalarTower ℚ Laurent (OverlapRing) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

def overlapBasis  : Module.Basis (Fin 8) Laurent (OverlapRing) :=
  (affineBasis).localizationLocalization Laurent
    (Submonoid.powers (Polynomial.X:Poly)) (OverlapRing)
@[simp] theorem overlapBasis_apply  (i : Fin 8) :
    overlapBasis i=algebraMap (AffineRing) (OverlapRing) (affineBasis i) :=
  Module.Basis.localizationLocalization_apply _ _ _ _ i

def overlapCoordinates  : OverlapRing≃ₗ[ℚ]ThirdTwistCoverLaurent.EightLaurent :=
  ((overlapBasis).repr.trans (Finsupp.linearEquivFunOnFinite Laurent Laurent (Fin 8))).restrictScalars ℚ

def affineRestriction  : AffineRing→ₗ[ℚ]OverlapRing :=
  (IsScalarTower.toAlgHom ℚ (AffineRing) (OverlapRing)).toLinearMap
@[simp] theorem affineRestriction_apply  (c : AffineRing) :
    affineRestriction c=algebraMap (AffineRing) (OverlapRing) c := rfl

theorem overlapCoordinates_affineRestriction  (c : AffineRing) (i : Fin 8) :
    overlapCoordinates (affineRestriction c) i=Polynomial.toLaurent ((affineBasis).repr c i) := by
  change (overlapBasis).repr (algebraMap (AffineRing) (OverlapRing) c) i=_
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ c i

theorem overlapDenominators_eq  : overlapDenominators=Submonoid.powers (ThirdTwistCoverAffine.m) := by
  change (Submonoid.powers (Polynomial.X:Poly)).map (algebraMap Poly (AffineRing))=_
  rw [Submonoid.map_powers]
  congr 1
  exact TripleSquareCover.polynomialToCoordinate_X _
instance overlapAwayM  : IsLocalization.Away (ThirdTwistCoverAffine.m) (OverlapRing) := by
  change IsLocalization (Submonoid.powers (ThirdTwistCoverAffine.m)) (OverlapRing)
  rw [←overlapDenominators_eq]
  infer_instance

def mDenominator  : overlapDenominators := ⟨ThirdTwistCoverAffine.m,by
  change ∃p∈Submonoid.powers (Polynomial.X:Poly),algebraMap Poly (AffineRing) p=ThirdTwistCoverAffine.m
  exact ⟨Polynomial.X,⟨1,pow_one _⟩,TripleSquareCover.polynomialToCoordinate_X _⟩⟩
def mUnit  : (OverlapRing)ˣ := (IsLocalization.map_units (OverlapRing) (mDenominator)).unit
@[simp] theorem mUnit_val  : (mUnit:OverlapRing)=
    algebraMap (AffineRing) (OverlapRing) (ThirdTwistCoverAffine.m) :=
  (IsLocalization.map_units (OverlapRing) (mDenominator)).unit_spec

def inverseM  : OverlapRing := ↑(mUnit)⁻¹

theorem m_mul_inverseM  : algebraMap (AffineRing) (OverlapRing) (ThirdTwistCoverAffine.m)*inverseM=1 := by
  rw [←mUnit_val]
  exact Units.mul_inv _
theorem inverseM_mul_m  : inverseM*algebraMap (AffineRing) (OverlapRing) (ThirdTwistCoverAffine.m)=1 := by
  rw [←mUnit_val]
  exact Units.inv_mul _
end
end Z2Z4Rank6.ThirdTwistCoverOverlap
