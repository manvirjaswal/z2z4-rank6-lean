module

public import Z2Z4Rank6.GTorsionCoverOverlap
public import Z2Z4Rank6.GTorsionCoverEquations

@[expose] public section

/-! Infinity restriction for the signed torsion covers:
z↦m⁻¹,U↦u/m²,R↦r/m⁴, inside the affine localization. -/
namespace Z2Z4Rank6.GTorsionCoverOverlap
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial GTorsionCoverEquations

def reversePolynomial : Poly→+*Laurent := Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
@[simp] theorem reversePolynomial_X : reversePolynomial Polynomial.X=LaurentPolynomial.T (-1) :=
  Polynomial.eval₂_X _ _

theorem scalarLaurent_T_one (ε : Bool) : algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T 1)=
    algebraMap (AffineRing ε) (OverlapRing ε) (GTorsionCoverAffine.m ε) := by
  calc
    _=algebraMap Laurent (OverlapRing ε) (algebraMap Poly Laurent Polynomial.X) := by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    _=algebraMap Poly (OverlapRing ε) Polynomial.X :=
      (IsScalarTower.algebraMap_apply Poly Laurent (OverlapRing ε) _).symm
    _=algebraMap (AffineRing ε) (OverlapRing ε) (algebraMap Poly (AffineRing ε) Polynomial.X) :=
      IsScalarTower.algebraMap_apply Poly (AffineRing ε) (OverlapRing ε) _
    _=_ := by rw [show algebraMap Poly (AffineRing ε) Polynomial.X=GTorsionCoverAffine.m ε from
      DoubleSquareCover.polynomialToCoordinate_X _]

theorem scalarLaurent_T_neg_one (ε : Bool) :
    algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-1))=inverseM ε := by
  have hp : algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T 1)*
      algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-1))=1 := by
    rw [←map_mul,←LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  rw [scalarLaurent_T_one] at hp
  have hh := congrArg (fun z : OverlapRing ε=>inverseM ε*z) hp
  simpa only [←mul_assoc,inverseM_mul_m,one_mul,mul_one] using hh

theorem scalarLaurent_T_neg_nat (ε : Bool) (n : ℕ) :
    algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-(n:ℤ)))=(inverseM ε)^n := by
  have ht : (LaurentPolynomial.T (-(n:ℤ)):Laurent)=(LaurentPolynomial.T (-1))^n := by
    rw [LaurentPolynomial.T_pow]
    simp
  rw [ht,map_pow,scalarLaurent_T_neg_one]

abbrev affineMap (ε : Bool) : AffineRing ε→+*OverlapRing ε := algebraMap (AffineRing ε) (OverlapRing ε)

private theorem mapped_root_sq (ε : Bool) (i : Fin 2) :
    (affineMap ε (DoubleSquareCover.root (GTorsionCoverAffine.radicand ε) i))^2 =
      Polynomial.aeval (affineMap ε (GTorsionCoverAffine.m ε))
        (GTorsionCoverAffine.radicand ε i) := by
  have h := congrArg (affineMap ε) (GTorsionCoverAffine.root_sq ε i)
  rw [map_pow] at h
  rw [h]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ (AffineRing ε) (OverlapRing ε)) _ _).symm

def scaledRoot (ε : Bool) (i : Fin 2) : OverlapRing ε :=
  affineMap ε (DoubleSquareCover.root (GTorsionCoverAffine.radicand ε) i)*
    inverseM ε^(GTorsionCoverEquations.rootWeight i)

theorem scaledRoot_sq (ε : Bool) (i : Fin 2) :
    (scaledRoot ε i)^2=Polynomial.aeval (inverseM ε) (GTorsionCoverInfinity.radicand ε i) := by
  have h := (mapped_root_sq ε i).trans
    (GTorsionCoverEquations.aeval_affine (A:=OverlapRing ε) ε
      (affineMap ε (GTorsionCoverAffine.m ε)) i)
  have hn := GTorsionCoverEquations.normalized ε 1
    (affineMap ε (GTorsionCoverAffine.m ε))
    (affineMap ε (DoubleSquareCover.root (GTorsionCoverAffine.radicand ε) i)) (inverseM ε) i h
  rw [one_mul,m_mul_inverseM] at hn
  exact hn.trans (GTorsionCoverEquations.aeval_infinity (A:=OverlapRing ε) ε (inverseM ε) i).symm

/-- Quotient-ring restriction to the localization. -/
def infinityRestriction (ε : Bool) : InfinityRing ε→ₐ[ℚ]OverlapRing ε :=
  DoubleSquareCover.lift (GTorsionCoverInfinity.radicand ε) (inverseM ε) (scaledRoot ε) (scaledRoot_sq ε)

@[simp] theorem infinityRestriction_z (ε : Bool) : infinityRestriction ε (GTorsionCoverInfinity.z ε)=inverseM ε := by
  exact DoubleSquareCover.lift_parameter _ _ _ _
@[simp] theorem infinityRestriction_u (ε : Bool) : infinityRestriction ε (GTorsionCoverInfinity.U ε)=
    affineMap ε (GTorsionCoverAffine.u ε)*(inverseM ε)^2 := by
  simp only [infinityRestriction,DoubleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_r (ε : Bool) : infinityRestriction ε (GTorsionCoverInfinity.R ε)=
    affineMap ε (GTorsionCoverAffine.r ε)*(inverseM ε)^4 := by
  simp only [infinityRestriction,DoubleSquareCover.lift_root]
  rfl

theorem infinityRestriction_polynomial (ε : Bool) (p : Poly) :
    infinityRestriction ε (DoubleSquareCover.polynomialToCoordinate (GTorsionCoverInfinity.radicand ε) p)=
      algebraMap Laurent (OverlapRing ε) (reversePolynomial p) := by
  have hh : (infinityRestriction ε).toRingHom.comp
      (DoubleSquareCover.polynomialToCoordinate (GTorsionCoverInfinity.radicand ε))=
      (algebraMap Laurent (OverlapRing ε)).comp reversePolynomial := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp only [RingHom.comp_apply,DoubleSquareCover.polynomialToCoordinate_X,reversePolynomial_X]
      change infinityRestriction ε (GTorsionCoverInfinity.z ε)=
        algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-1))
      rw [infinityRestriction_z,scalarLaurent_T_neg_one]
  exact RingHom.congr_fun hh p
end
end Z2Z4Rank6.GTorsionCoverOverlap
