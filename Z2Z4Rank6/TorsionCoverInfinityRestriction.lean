import Z2Z4Rank6.TorsionCoverOverlap
import Z2Z4Rank6.TorsionCoverEquations

/-! Infinity restriction for the signed torsion covers:
z↦m⁻¹,U↦u/m,V↦v/m,R↦r/m⁴, inside the affine localization. -/
namespace Z2Z4Rank6.TorsionCoverOverlap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial TorsionCoverEquations

def reversePolynomial : Poly→+*Laurent := Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
@[simp] theorem reversePolynomial_X : reversePolynomial Polynomial.X=LaurentPolynomial.T (-1) :=
  Polynomial.eval₂_X _ _

theorem scalarLaurent_T_one (ε : Bool) : algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T 1)=
    algebraMap (AffineRing ε) (OverlapRing ε) (TorsionCoverAffine.m ε) := by
  calc
    _=algebraMap Laurent (OverlapRing ε) (algebraMap Poly Laurent Polynomial.X) := by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    _=algebraMap Poly (OverlapRing ε) Polynomial.X :=
      (IsScalarTower.algebraMap_apply Poly Laurent (OverlapRing ε) _).symm
    _=algebraMap (AffineRing ε) (OverlapRing ε) (algebraMap Poly (AffineRing ε) Polynomial.X) :=
      IsScalarTower.algebraMap_apply Poly (AffineRing ε) (OverlapRing ε) _
    _=_ := by rw [show algebraMap Poly (AffineRing ε) Polynomial.X=TorsionCoverAffine.m ε from
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

theorem mapped_u_sq (ε : Bool) : (affineMap ε (TorsionCoverAffine.u ε))^2=
    15*(affineMap ε (TorsionCoverAffine.m ε))^2+1210 := by
  have h := congrArg (affineMap ε) (TorsionCoverAffine.u_sq ε)
  simpa only [map_pow,map_add,map_mul,map_ofNat] using h

theorem mapped_v_sq (ε : Bool) : (affineMap ε (TorsionCoverAffine.v ε))^2=
    10*(affineMap ε (TorsionCoverAffine.m ε))^2+1215 := by
  have h := congrArg (affineMap ε) (TorsionCoverAffine.v_sq ε)
  simpa only [map_pow,map_add,map_mul,map_ofNat] using h

theorem mapped_r_sq (ε : Bool) : (affineMap ε (TorsionCoverAffine.r ε))^2=
    algebraMap ℚ (OverlapRing ε) (TorsionHyperelliptic.sign ε)*
      a (affineMap ε (TorsionCoverAffine.m ε))*b (affineMap ε (TorsionCoverAffine.m ε)) := by
  have h := congrArg (affineMap ε) (TorsionCoverAffine.r_sq ε)
  have hs := (affineMap ε).map_rat_algebraMap (TorsionHyperelliptic.sign ε)
  have ha := TorsionCoverEquations.map_a (A:=AffineRing ε) (B:=OverlapRing ε) (affineMap ε) (TorsionCoverAffine.m ε)
  have hb := TorsionCoverEquations.map_b (A:=AffineRing ε) (B:=OverlapRing ε) (affineMap ε) (TorsionCoverAffine.m ε)
  rw [map_pow,map_mul,map_mul,hs,ha,hb] at h
  exact h

def scaledRoot (ε : Bool) : Fin 3→OverlapRing ε :=
  ![affineMap ε (TorsionCoverAffine.u ε)*inverseM ε,
    affineMap ε (TorsionCoverAffine.v ε)*inverseM ε,
    affineMap ε (TorsionCoverAffine.r ε)*(inverseM ε)^4]

theorem scaledRoot_sq (ε : Bool) (i : Fin 3) :
    (scaledRoot ε i)^2=Polynomial.aeval (inverseM ε) (TorsionCoverInfinity.radicand ε i) := by
  fin_cases i
  · change (affineMap ε (TorsionCoverAffine.u ε)*inverseM ε)^2=
      Polynomial.aeval (inverseM ε) (15+1210*Polynomial.X^2)
    simp only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X]
    exact (scaled_square (A:=OverlapRing ε) (affineMap ε (TorsionCoverAffine.m ε))
      (affineMap ε (TorsionCoverAffine.u ε)) (inverseM ε) 15 1210 (mapped_u_sq ε) (m_mul_inverseM ε)).trans
        (add_comm (1210*(inverseM ε)^2) 15)
  · change (affineMap ε (TorsionCoverAffine.v ε)*inverseM ε)^2=
      Polynomial.aeval (inverseM ε) (10+1215*Polynomial.X^2)
    simp only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X]
    exact (scaled_square (A:=OverlapRing ε) (affineMap ε (TorsionCoverAffine.m ε))
      (affineMap ε (TorsionCoverAffine.v ε)) (inverseM ε) 10 1215 (mapped_v_sq ε) (m_mul_inverseM ε)).trans
        (add_comm (1215*(inverseM ε)^2) 10)
  · change (affineMap ε (TorsionCoverAffine.r ε)*(inverseM ε)^4)^2=
      Polynomial.aeval (inverseM ε) (Polynomial.C (TorsionHyperelliptic.sign ε)*
        HeightInvariantForms.binaryA (Polynomial.X:Poly) 1*HeightInvariantForms.binaryB Polynomial.X 1)
    simp only [map_mul,Polynomial.aeval_C,
      aeval_binaryA (A:=OverlapRing ε) (inverseM ε),aeval_binaryB (A:=OverlapRing ε) (inverseM ε)]
    rw [binaryA_inverse (affineMap ε (TorsionCoverAffine.m ε)) (inverseM ε) (inverseM_mul_m ε),
      binaryB_inverse (affineMap ε (TorsionCoverAffine.m ε)) (inverseM ε) (inverseM_mul_m ε)]
    calc
      _=(affineMap ε (TorsionCoverAffine.r ε))^2*(inverseM ε)^8 := by ring
      _=_ := by rw [mapped_r_sq]; ring

/-- Quotient-ring restriction to the localization. -/
def infinityRestriction (ε : Bool) : InfinityRing ε→ₐ[ℚ]OverlapRing ε :=
  TripleSquareCover.lift (TorsionCoverInfinity.radicand ε) (inverseM ε) (scaledRoot ε) (scaledRoot_sq ε)

@[simp] theorem infinityRestriction_z (ε : Bool) : infinityRestriction ε (TorsionCoverInfinity.z ε)=inverseM ε := by
  exact TripleSquareCover.lift_parameter _ _ _ _
@[simp] theorem infinityRestriction_u (ε : Bool) : infinityRestriction ε (TorsionCoverInfinity.U ε)=
    affineMap ε (TorsionCoverAffine.u ε)*inverseM ε := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_v (ε : Bool) : infinityRestriction ε (TorsionCoverInfinity.V ε)=
    affineMap ε (TorsionCoverAffine.v ε)*inverseM ε := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl
@[simp] theorem infinityRestriction_r (ε : Bool) : infinityRestriction ε (TorsionCoverInfinity.R ε)=
    affineMap ε (TorsionCoverAffine.r ε)*(inverseM ε)^4 := by
  simp only [infinityRestriction,TripleSquareCover.lift_root]
  rfl

theorem infinityRestriction_polynomial (ε : Bool) (p : Poly) :
    infinityRestriction ε (TripleSquareCover.polynomialToCoordinate (TorsionCoverInfinity.radicand ε) p)=
      algebraMap Laurent (OverlapRing ε) (reversePolynomial p) := by
  have hh : (infinityRestriction ε).toRingHom.comp
      (TripleSquareCover.polynomialToCoordinate (TorsionCoverInfinity.radicand ε))=
      (algebraMap Laurent (OverlapRing ε)).comp reversePolynomial := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · simp only [RingHom.comp_apply,TripleSquareCover.polynomialToCoordinate_X,reversePolynomial_X]
      change infinityRestriction ε (TorsionCoverInfinity.z ε)=
        algebraMap Laurent (OverlapRing ε) (LaurentPolynomial.T (-1))
      rw [infinityRestriction_z,scalarLaurent_T_neg_one]
  exact RingHom.congr_fun hh p
end
end Z2Z4Rank6.TorsionCoverOverlap
