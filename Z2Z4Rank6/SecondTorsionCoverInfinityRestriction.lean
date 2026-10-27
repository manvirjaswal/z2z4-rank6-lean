import Z2Z4Rank6.SecondTorsionCoverOverlap
import Z2Z4Rank6.TorsionCoverEquations

/-! Infinity restriction for the signed torsion covers:
z↦m⁻¹,U↦u/m,V↦v/m,R↦r/m², inside the affine localization. -/
namespace Z2Z4Rank6.SecondTorsionCoverOverlap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial TorsionCoverEquations SecondFamily

def reversePolynomial : Poly→+*Laurent := Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
@[simp] theorem reversePolynomial_X : reversePolynomial Polynomial.X=LaurentPolynomial.T (-1) :=
  Polynomial.eval₂_X _ _

theorem scalarLaurent_T_one (ε : Bool) : algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T 1)=
    algebraMap (AffineRing ε) (OverlapRing ε) (SecondTorsionCoverAffine.m ε) := by
  calc
    _=algebraMap Laurent (OverlapRing ε) (algebraMap Poly Laurent Polynomial.X) := by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    _=algebraMap Poly (OverlapRing ε) Polynomial.X :=
      (IsScalarTower.algebraMap_apply Poly Laurent (OverlapRing ε) _).symm
    _=algebraMap (AffineRing ε) (OverlapRing ε) (algebraMap Poly (AffineRing ε) Polynomial.X) :=
      IsScalarTower.algebraMap_apply Poly (AffineRing ε) (OverlapRing ε) _
    _=_ := by rw [show algebraMap Poly (AffineRing ε) Polynomial.X=SecondTorsionCoverAffine.m ε from
      TripleSquareCover.polynomialToCoordinate_X _]

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

private theorem mapped_root_sq (ε : Bool) (i : Fin 3) :
    (affineMap ε (TripleSquareCover.root (SecondTorsionCoverAffine.radicand ε) i))^2 =
      Polynomial.aeval (affineMap ε (SecondTorsionCoverAffine.m ε))
        (SecondTorsionCoverAffine.radicand ε i) := by
  have h := congrArg (affineMap ε) (SecondTorsionCoverAffine.root_sq ε i)
  rw [map_pow] at h
  rw [h]
  exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℚ (AffineRing ε) (OverlapRing ε)) _ _).symm

def scaledRoot (ε : Bool) : Fin 3→OverlapRing ε :=
  ![affineMap ε (SecondTorsionCoverAffine.u ε)*inverseM ε,
    affineMap ε (SecondTorsionCoverAffine.v ε)*inverseM ε,
    affineMap ε (SecondTorsionCoverAffine.r ε)*(inverseM ε)^2]

theorem scaledRoot_sq (ε : Bool) (i : Fin 3) :
    (scaledRoot ε i)^2=Polynomial.aeval (inverseM ε) (SecondTorsionCoverInfinity.radicand ε i) := by
  have hm := m_mul_inverseM ε
  have hm2 : (affineMap ε (SecondTorsionCoverAffine.m ε))^2*(inverseM ε)^2=1 := by
    calc
      _=(affineMap ε (SecondTorsionCoverAffine.m ε)*inverseM ε)^2 := by ring
      _=1 := by rw [hm]; norm_num
  have h := mapped_root_sq ε i
  fin_cases i
  · change (affineMap ε (SecondTorsionCoverAffine.u ε)*inverseM ε)^2=
      Polynomial.aeval (inverseM ε) (29*(1-Polynomial.C (beta:ℚ)*Polynomial.X^2))
    change (affineMap ε (SecondTorsionCoverAffine.u ε))^2=
      Polynomial.aeval (affineMap ε (SecondTorsionCoverAffine.m ε)) (29*(Polynomial.X^2-Polynomial.C (beta:ℚ))) at h
    simp only [map_mul,map_sub,map_pow,map_one,map_ofNat,Polynomial.aeval_X,Polynomial.aeval_C] at h ⊢
    calc
      _=(29*((affineMap ε (SecondTorsionCoverAffine.m ε))^2-algebraMap ℚ (OverlapRing ε) beta))*(inverseM ε)^2 := by rw [←h]; ring
      _=_ := by linear_combination 29*hm2
  · change (affineMap ε (SecondTorsionCoverAffine.v ε)*inverseM ε)^2=
      Polynomial.aeval (inverseM ε) (Polynomial.C (-29*(beta:ℚ))*(1-Polynomial.C (gamma:ℚ)*Polynomial.X^2))
    change (affineMap ε (SecondTorsionCoverAffine.v ε))^2=
      Polynomial.aeval (affineMap ε (SecondTorsionCoverAffine.m ε)) (Polynomial.C (-29*(beta:ℚ))*(Polynomial.X^2-Polynomial.C (gamma:ℚ))) at h
    simp only [map_mul,map_sub,map_pow,map_one,Polynomial.aeval_X,Polynomial.aeval_C] at h ⊢
    linear_combination (inverseM ε)^2*h +
      ((algebraMap ℚ (OverlapRing ε) (-29))*(algebraMap ℚ (OverlapRing ε) (beta:ℚ)))*hm2

  · change (affineMap ε (SecondTorsionCoverAffine.r ε)*(inverseM ε)^2)^2=
      Polynomial.aeval (inverseM ε) (-Polynomial.C (TorsionHyperelliptic.sign ε)*(1-Polynomial.X^2)*(1-Polynomial.C ((lambda:ℚ)^2)*Polynomial.X^2))
    change (affineMap ε (SecondTorsionCoverAffine.r ε))^2=
      Polynomial.aeval (affineMap ε (SecondTorsionCoverAffine.m ε)) (-Polynomial.C (TorsionHyperelliptic.sign ε)*(Polynomial.X^2-1)*(Polynomial.X^2-Polynomial.C ((lambda:ℚ)^2))) at h
    simp only [map_mul,map_sub,map_pow,map_neg,map_one,Polynomial.aeval_X,Polynomial.aeval_C] at h ⊢
    have h1 : ((affineMap ε (SecondTorsionCoverAffine.m ε))^2-1)*(inverseM ε)^2=1-(inverseM ε)^2 := by linear_combination hm2
    have h2 : ((affineMap ε (SecondTorsionCoverAffine.m ε))^2-(algebraMap ℚ (OverlapRing ε) (lambda:ℚ))^2)*(inverseM ε)^2=
        1-(algebraMap ℚ (OverlapRing ε) (lambda:ℚ))^2*(inverseM ε)^2 := by linear_combination hm2
    calc
      _=(affineMap ε (SecondTorsionCoverAffine.r ε))^2*(inverseM ε)^4 := by ring
      _= -algebraMap ℚ (OverlapRing ε) (TorsionHyperelliptic.sign ε)*
          (((affineMap ε (SecondTorsionCoverAffine.m ε))^2-1)*(inverseM ε)^2)*
          (((affineMap ε (SecondTorsionCoverAffine.m ε))^2-(algebraMap ℚ (OverlapRing ε) (lambda:ℚ))^2)*(inverseM ε)^2) := by rw [h]; ring
      _=_ := by rw [h1,h2]

/-- Quotient-ring restriction to the localization. -/
def infinityRestriction (ε : Bool) : InfinityRing ε→ₐ[ℚ]OverlapRing ε :=
  TripleSquareCover.lift (SecondTorsionCoverInfinity.radicand ε) (inverseM ε) (scaledRoot ε) (scaledRoot_sq ε)

@[simp] theorem infinityRestriction_z (ε : Bool) : infinityRestriction ε (SecondTorsionCoverInfinity.z ε)=inverseM ε := by
  exact TripleSquareCover.lift_parameter _ _ _ _
@[simp] theorem infinityRestriction_u (ε : Bool) : infinityRestriction ε (SecondTorsionCoverInfinity.U ε)=
    affineMap ε (SecondTorsionCoverAffine.u ε)*inverseM ε := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_v (ε : Bool) : infinityRestriction ε (SecondTorsionCoverInfinity.V ε)=
    affineMap ε (SecondTorsionCoverAffine.v ε)*inverseM ε := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_r (ε : Bool) : infinityRestriction ε (SecondTorsionCoverInfinity.R ε)=
    affineMap ε (SecondTorsionCoverAffine.r ε)*(inverseM ε)^2 := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl

theorem infinityRestriction_polynomial (ε : Bool) (p : Poly) :
    infinityRestriction ε (TripleSquareCover.polynomialToCoordinate (SecondTorsionCoverInfinity.radicand ε) p)=
      algebraMap Laurent (OverlapRing ε) (reversePolynomial p) := by
  have hh : (infinityRestriction ε).toRingHom.comp
      (TripleSquareCover.polynomialToCoordinate (SecondTorsionCoverInfinity.radicand ε))=
      (algebraMap Laurent (OverlapRing ε)).comp reversePolynomial := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp only [RingHom.comp_apply,TripleSquareCover.polynomialToCoordinate_X,reversePolynomial_X]
      change infinityRestriction ε (SecondTorsionCoverInfinity.z ε)=
        algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-1))
      rw [infinityRestriction_z,scalarLaurent_T_neg_one]
  exact RingHom.congr_fun hh p
end
end Z2Z4Rank6.SecondTorsionCoverOverlap
