module

public import Z2Z4Rank6.SecondTorsionCoverNormalForm
public import Z2Z4Rank6.SecondTorsionCoverLaurent
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

/-! The signed torsion-cover affine overlap, obtained by inverting m,
and its free eight-coefficient Laurent coordinates. -/
namespace Z2Z4Rank6.SecondTorsionCoverOverlap
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev Laurent := LaurentPolynomial ℚ
abbrev AffineRing := SecondTorsionCoverAffine.CoordinateRing
abbrev InfinityRing := SecondTorsionCoverInfinity.CoordinateRing
abbrev affineBasis (ε : Bool) := SecondTorsionCoverAffine.basis ε
abbrev infinityBasis (ε : Bool) := SecondTorsionCoverInfinity.basis ε
abbrev overlapDenominators (ε : Bool) := Algebra.algebraMapSubmonoid (AffineRing ε)
  (Submonoid.powers (Polynomial.X:Poly))
abbrev OverlapRing (ε : Bool) := Localization (overlapDenominators ε)

instance overlapLaurentAlgebra (ε : Bool) : Algebra Laurent (OverlapRing ε) :=
  localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing ε)
    (Submonoid.powers (Polynomial.X:Poly)) (AffineRing ε)
instance overlapPolyLaurentTower (ε : Bool) : IsScalarTower Poly Laurent (OverlapRing ε) :=
  isScalarTower_localizationAlgebra (Rₘ:=Laurent) (Sₘ:=OverlapRing ε)
    (Submonoid.powers (Polynomial.X:Poly)) (AffineRing ε)
instance overlapRatLaurentTower (ε : Bool) : IsScalarTower ℚ Laurent (OverlapRing ε) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

def overlapBasis (ε : Bool) : Module.Basis (Fin 8) Laurent (OverlapRing ε) :=
  (affineBasis ε).localizationLocalization Laurent
    (Submonoid.powers (Polynomial.X:Poly)) (OverlapRing ε)
@[simp] theorem overlapBasis_apply (ε : Bool) (i : Fin 8) :
    overlapBasis ε i=algebraMap (AffineRing ε) (OverlapRing ε) (affineBasis ε i) :=
  Module.Basis.localizationLocalization_apply _ _ _ _ i

def overlapCoordinates (ε : Bool) : OverlapRing ε≃ₗ[ℚ]SecondTorsionCoverLaurent.EightLaurent :=
  ((overlapBasis ε).repr.trans (Finsupp.linearEquivFunOnFinite Laurent Laurent (Fin 8))).restrictScalars ℚ

def affineRestriction (ε : Bool) : AffineRing ε→ₗ[ℚ]OverlapRing ε :=
  (IsScalarTower.toAlgHom ℚ (AffineRing ε) (OverlapRing ε)).toLinearMap
@[simp] theorem affineRestriction_apply (ε : Bool) (c : AffineRing ε) :
    affineRestriction ε c=algebraMap (AffineRing ε) (OverlapRing ε) c := rfl

theorem overlapCoordinates_affineRestriction (ε : Bool) (c : AffineRing ε) (i : Fin 8) :
    overlapCoordinates ε (affineRestriction ε c) i=Polynomial.toLaurent ((affineBasis ε).repr c i) := by
  change (overlapBasis ε).repr (algebraMap (AffineRing ε) (OverlapRing ε) c) i=_
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ c i

theorem overlapDenominators_eq (ε : Bool) : overlapDenominators ε=Submonoid.powers (SecondTorsionCoverAffine.m ε) := by
  change (Submonoid.powers (Polynomial.X:Poly)).map (algebraMap Poly (AffineRing ε))=_
  rw [Submonoid.map_powers]
  congr 1
  exact TripleSquareCover.polynomialToCoordinate_X _
instance overlapAwayM (ε : Bool) : IsLocalization.Away (SecondTorsionCoverAffine.m ε) (OverlapRing ε) := by
  change IsLocalization (Submonoid.powers (SecondTorsionCoverAffine.m ε)) (OverlapRing ε)
  rw [←overlapDenominators_eq]
  infer_instance

def mDenominator (ε : Bool) : overlapDenominators ε := ⟨SecondTorsionCoverAffine.m ε,by
  change ∃p∈Submonoid.powers (Polynomial.X:Poly),algebraMap Poly (AffineRing ε) p=SecondTorsionCoverAffine.m ε
  exact ⟨Polynomial.X,⟨1,pow_one _⟩,TripleSquareCover.polynomialToCoordinate_X _⟩⟩
def mUnit (ε : Bool) : (OverlapRing ε)ˣ := (IsLocalization.map_units (OverlapRing ε) (mDenominator ε)).unit
@[simp] theorem mUnit_val (ε : Bool) : (mUnit ε:OverlapRing ε)=
    algebraMap (AffineRing ε) (OverlapRing ε) (SecondTorsionCoverAffine.m ε) :=
  (IsLocalization.map_units (OverlapRing ε) (mDenominator ε)).unit_spec

def inverseM (ε : Bool) : OverlapRing ε := ↑(mUnit ε)⁻¹

theorem m_mul_inverseM (ε : Bool) : algebraMap (AffineRing ε) (OverlapRing ε) (SecondTorsionCoverAffine.m ε)*inverseM ε=1 := by
  rw [←mUnit_val]
  exact Units.mul_inv _
theorem inverseM_mul_m (ε : Bool) : inverseM ε*algebraMap (AffineRing ε) (OverlapRing ε) (SecondTorsionCoverAffine.m ε)=1 := by
  rw [←mUnit_val]
  exact Units.inv_mul _
end
end Z2Z4Rank6.SecondTorsionCoverOverlap
