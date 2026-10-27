module

public import Z2Z4Rank6.ThirdTwistCoverOverlap
public import Z2Z4Rank6.ThirdTwistCoverEquations

@[expose] public section

/-! Infinity restriction for the third-twist base:
z↦m⁻¹,U↦u/m,V↦v/m,W↦w/m, inside the affine localization. -/
namespace Z2Z4Rank6.ThirdTwistCoverOverlap
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial ThirdTwistCoverEquations

def reversePolynomial : Poly→+*Laurent := Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
@[simp] theorem reversePolynomial_X : reversePolynomial Polynomial.X=LaurentPolynomial.T (-1) :=
  Polynomial.eval₂_X _ _

theorem scalarLaurent_T_one  : algebraMap Laurent (OverlapRing) (LaurentPolynomial.T 1)=
    algebraMap (AffineRing) (OverlapRing) (ThirdTwistCoverAffine.m) := by
  calc
    _=algebraMap Laurent (OverlapRing) (algebraMap Poly Laurent Polynomial.X) := by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    _=algebraMap Poly (OverlapRing) Polynomial.X :=
      (IsScalarTower.algebraMap_apply Poly Laurent (OverlapRing) _).symm
    _=algebraMap (AffineRing) (OverlapRing) (algebraMap Poly (AffineRing) Polynomial.X) :=
      IsScalarTower.algebraMap_apply Poly (AffineRing) (OverlapRing) _
    _=_ := by rw [show algebraMap Poly (AffineRing) Polynomial.X=ThirdTwistCoverAffine.m from
      TripleSquareCover.polynomialToCoordinate_X _]

theorem scalarLaurent_T_neg_one  :
    algebraMap Laurent (OverlapRing) (LaurentPolynomial.T (-1))=inverseM := by
  have hp : algebraMap Laurent (OverlapRing) (LaurentPolynomial.T 1)*
      algebraMap Laurent (OverlapRing) (LaurentPolynomial.T (-1))=1 := by
    rw [←map_mul,←LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  rw [scalarLaurent_T_one] at hp
  have hh := congrArg (fun z : OverlapRing=>inverseM*z) hp
  simpa only [←mul_assoc,inverseM_mul_m,one_mul,mul_one] using hh

theorem scalarLaurent_T_neg_nat  (n : ℕ) :
    algebraMap Laurent (OverlapRing) (LaurentPolynomial.T (-(n:ℤ)))=(inverseM)^n := by
  have ht : (LaurentPolynomial.T (-(n:ℤ)):Laurent)=(LaurentPolynomial.T (-1))^n := by
    rw [LaurentPolynomial.T_pow]
    simp
  rw [ht,map_pow,scalarLaurent_T_neg_one]

abbrev affineMap  : AffineRing→+*OverlapRing := algebraMap (AffineRing) (OverlapRing)

private theorem mapped_root_sq  (i : Fin 3) :
    (affineMap (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) i))^2 =
      Polynomial.aeval (affineMap (ThirdTwistCoverAffine.m))
        (ThirdTwistCoverAffine.radicand i) := by
  have h := congrArg (affineMap) (ThirdTwistCoverAffine.root_sq i)
  rw [map_pow] at h
  rw [h]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ (AffineRing) (OverlapRing)) _ _).symm

def scaledRoot  (i : Fin 3) : OverlapRing :=
  affineMap (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) i)*
    inverseM^(ThirdTwistCoverEquations.rootWeight i)

theorem scaledRoot_sq  (i : Fin 3) :
    (scaledRoot i)^2=Polynomial.aeval (inverseM) (ThirdTwistCoverInfinity.radicand i) := by
  have h := (mapped_root_sq i).trans
    (ThirdTwistCoverEquations.aeval_affine (A:=OverlapRing)
      (affineMap (ThirdTwistCoverAffine.m)) i)
  have hn := ThirdTwistCoverEquations.normalized 1
    (affineMap (ThirdTwistCoverAffine.m))
    (affineMap (TripleSquareCover.root (ThirdTwistCoverAffine.radicand) i)) (inverseM) i h
  rw [one_mul,m_mul_inverseM] at hn
  exact hn.trans (ThirdTwistCoverEquations.aeval_infinity (A:=OverlapRing) (inverseM) i).symm

/-- Quotient-ring restriction to the localization. -/
def infinityRestriction  : InfinityRing→ₐ[ℚ]OverlapRing :=
  TripleSquareCover.lift (ThirdTwistCoverInfinity.radicand) (inverseM) (scaledRoot) (scaledRoot_sq)

@[simp] theorem infinityRestriction_z  : infinityRestriction (ThirdTwistCoverInfinity.z)=inverseM := by
  exact TripleSquareCover.lift_parameter _ _ _ _
@[simp] theorem infinityRestriction_u  : infinityRestriction (ThirdTwistCoverInfinity.U)=
    affineMap (ThirdTwistCoverAffine.u)*(inverseM)^1 := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_v : infinityRestriction ThirdTwistCoverInfinity.V=
    affineMap ThirdTwistCoverAffine.v*(inverseM)^1 := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_r  : infinityRestriction (ThirdTwistCoverInfinity.R)=
    affineMap (ThirdTwistCoverAffine.r)*(inverseM)^1 := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl

theorem infinityRestriction_polynomial  (p : Poly) :
    infinityRestriction (TripleSquareCover.polynomialToCoordinate (ThirdTwistCoverInfinity.radicand) p)=
      algebraMap Laurent (OverlapRing) (reversePolynomial p) := by
  have hh : (infinityRestriction).toRingHom.comp
      (TripleSquareCover.polynomialToCoordinate (ThirdTwistCoverInfinity.radicand))=
      (algebraMap Laurent (OverlapRing)).comp reversePolynomial := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp only [RingHom.comp_apply,TripleSquareCover.polynomialToCoordinate_X,reversePolynomial_X]
      change infinityRestriction (ThirdTwistCoverInfinity.z)=
        algebraMap Laurent (OverlapRing) (LaurentPolynomial.T (-1))
      rw [infinityRestriction_z,scalarLaurent_T_neg_one]
  exact RingHom.congr_fun hh p
end
end Z2Z4Rank6.ThirdTwistCoverOverlap
