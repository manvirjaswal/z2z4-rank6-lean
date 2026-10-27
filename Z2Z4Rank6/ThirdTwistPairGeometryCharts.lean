import Z2Z4Rank6.ThirdTwistPairGeometryAffine
import Z2Z4Rank6.WeightedProjectiveChartHelpers
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! The z-chart of each two-quadric projective base is exactly its
affine two-square quotient. Both maps and inverse identities are
proved on the homogeneous localization and quotient rings. -/
namespace Z2Z4Rank6.ThirdTwistPairGeometry
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Charts

theorem degreeZero_eq_rat (ε : Bool) (r : grading ε 0) :
    ∃q : ℚ,r=algebraMap ℚ (grading ε 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.totalDegree=0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr hp
  have hpC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hp0
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing ε)=algebraMap ℚ (CoordinateRing ε) (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

theorem coordinate_adjoin (ε : Bool) :
    Algebra.adjoin (grading ε 0) (Set.range (coordinate ε))=⊤ := by
  have hpoly : ∀ p : PolynomialRing,Ideal.Quotient.mk (definingIdeal ε) p∈
      Algebra.adjoin (grading ε 0) (Set.range (coordinate ε)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
      have h0 : Ideal.Quotient.mk (definingIdeal ε) (C r)∈grading ε 0 :=
        ⟨C r,isHomogeneous_C (Fin 4) r,rfl⟩
      exact (Algebra.adjoin (grading ε 0) (Set.range (coordinate ε))).algebraMap_mem
        ⟨Ideal.Quotient.mk (definingIdeal ε) (C r),h0⟩
    | add p q hp hq => simpa only [map_add] using add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul,coordinate] using mul_mem hp
        (Algebra.subset_adjoin (show coordinate ε i∈Set.range (coordinate ε) from ⟨i,rfl⟩))
  apply top_unique
  intro x _
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hpoly p

abbrev ChartRing (ε : Bool) := HomogeneousLocalization.Away (grading ε) (z ε)
abbrev LocalizedRing (ε : Bool) := Localization.Away (z ε)
instance chartAlgebra (ε : Bool) : Algebra ℚ (ChartRing ε) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading ε) (Submonoid.powers (z ε))).comp
    (algebraMap ℚ (grading ε 0))).toAlgebra

def ratio (ε : Bool) (i : Fin 4) : ChartRing ε :=
  WeightedProjectiveChartHelpers.fraction (grading ε) (coordinate_degree ε 3)
    1 (coordinate ε i) (coordinate_degree ε i)
abbrev inverseCoordinate (ε : Bool) : LocalizedRing ε := IsLocalization.Away.invSelf (z ε)

theorem coordinate_mul_inverse (ε : Bool) :
    algebraMap (CoordinateRing ε) (LocalizedRing ε) (z ε)*inverseCoordinate ε=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (ε : Bool) (i : Fin 4) :
    (ratio ε i).val=algebraMap (CoordinateRing ε) (LocalizedRing ε) (coordinate ε i)*
      inverseCoordinate ε := by
  rw [ratio,WeightedProjectiveChartHelpers.fraction_val,pow_one]
  rfl

@[simp] theorem ratio_self (ε : Bool) : ratio ε 3=1 :=
  WeightedProjectiveChartHelpers.fraction_self _ _

theorem scalar_val (ε : Bool) (q : ℚ) :
    (algebraMap ℚ (ChartRing ε) q).val=
      algebraMap (CoordinateRing ε) (LocalizedRing ε) (algebraMap ℚ (CoordinateRing ε) q) := by
  change Localization.mk (algebraMap ℚ (CoordinateRing ε) q)
    (1:Submonoid.powers (z ε))=_
  exact Localization.mk_one_eq_algebraMap _

theorem chartRingHom_ext {S : Type*} [CommRing S] (ε : Bool)
    (F G : ChartRing ε →+* S) (h : ∀i,F (ratio ε i)=G (ratio ε i)) : F=G :=
  WeightedProjectiveChartHelpers.ringHom_ext _ (coordinate_degree ε 3) (coordinate ε)
    (fun _=>1) (coordinate_degree ε) (coordinate_adjoin ε) (degreeZero_eq_rat ε) F G h

private theorem normalize_square {R : Type*} [CommRing R] (s t z a b r : R)
    (hs : s^2=a*t^2+b*z^2) (hz : z*r=1) : (s*r)^2=a*(t*r)^2+b := by
  have hh := congrArg (fun x : R=>x^2) hz
  linear_combination r^2*hs+b*hh

theorem ratio_u_sq (ε : Bool) :
    (ratio ε 1)^2=algebraMap ℚ (ChartRing ε) (leading ε)*(ratio ε 0)^2+
      algebraMap ℚ (ChartRing ε) (constant ε) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val,scalar_val]
  apply normalize_square
  · have h := congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε))
      (ThirdTwistPairGeometry.u_sq ε)
    simpa only [map_pow,map_add,map_mul] using h
  · exact coordinate_mul_inverse ε

theorem ratio_w_sq (ε : Bool) : (ratio ε 2)^2=4*(ratio ε 0)^2+45 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_pow,HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_mul,ratio_val]
  norm_num only [←HomogeneousLocalization.algebraMap_apply,map_ofNat]
  apply normalize_square
  · have h := congrArg (algebraMap (CoordinateRing ε) (LocalizedRing ε))
      (ThirdTwistPairGeometry.w_sq ε)
    simpa only [map_pow,map_add,map_mul,map_ofNat] using h
  · exact coordinate_mul_inverse ε

def atZOne (ε : Bool) : CoordinateRing ε →ₐ[ℚ] Affine.CoordinateRing ε :=
  Ideal.Quotient.liftₐ (definingIdeal ε)
    (MvPolynomial.aeval ![Affine.m ε,Affine.u ε,Affine.w ε,1]) (by
      have hker : definingIdeal ε≤RingHom.ker
          (MvPolynomial.aeval ![Affine.m ε,Affine.u ε,Affine.w ε,1]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval ![Affine.m ε,Affine.u ε,Affine.w ε,1]) (relation ε i)=0
        fin_cases i
        · change (MvPolynomial.aeval ![Affine.m ε,Affine.u ε,Affine.w ε,1])
            (MvPolynomial.X 1^2-C (leading ε)*MvPolynomial.X 0^2-
              C (constant ε)*MvPolynomial.X 3^2)=0
          simp only [map_sub,map_pow,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
          change (Affine.u ε)^2-algebraMap ℚ (Affine.CoordinateRing ε) (leading ε)*(Affine.m ε)^2-
            algebraMap ℚ (Affine.CoordinateRing ε) (constant ε)*1^2=0
          linear_combination Affine.u_sq ε
        · change (MvPolynomial.aeval ![Affine.m ε,Affine.u ε,Affine.w ε,1])
            (MvPolynomial.X 2^2-C (4:ℚ)*MvPolynomial.X 0^2-C (45:ℚ)*MvPolynomial.X 3^2)=0
          simp only [map_sub,map_pow,map_mul,MvPolynomial.aeval_X,MvPolynomial.aeval_C]
          norm_num only [map_ofNat]
          change (Affine.w ε)^2-4*(Affine.m ε)^2-45*1^2=0
          linear_combination Affine.w_sq ε
      intro p hp
      exact hker hp)

@[simp] theorem atZOne_coordinate (ε : Bool) (i : Fin 4) :
    atZOne ε (coordinate ε i)=![Affine.m ε,Affine.u ε,Affine.w ε,1] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def chartToAffine (ε : Bool) : ChartRing ε →ₐ[ℚ] Affine.CoordinateRing ε :=
  ((Localization.awayLift (atZOne ε).toRingHom (z ε) (by simp)).comp
    (algebraMap (ChartRing ε) (LocalizedRing ε))).toRatAlgHom

@[simp] theorem chartToAffine_ratio (ε : Bool) (i : Fin 4) :
    chartToAffine ε (ratio ε i)=![Affine.m ε,Affine.u ε,Affine.w ε,1] i := by
  change Localization.awayLift (atZOne ε).toRingHom (z ε) (by simp) (ratio ε i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : (Localization.awayLift (atZOne ε).toRingHom (z ε) (by simp)) (inverseCoordinate ε)=1 := by
    have h := congrArg (Localization.awayLift (atZOne ε).toRingHom (z ε) (by simp))
      (coordinate_mul_inverse ε)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change atZOne ε (coordinate ε 3)*_=1 at h
    simpa using h
  rw [hi,mul_one]
  exact atZOne_coordinate ε i

def affineToChart (ε : Bool) : Affine.CoordinateRing ε →ₐ[ℚ] ChartRing ε :=
  DoubleSquareCover.lift (radicand ε) (ratio ε 0) ![ratio ε 1,ratio ε 2] (by
    intro i
    fin_cases i
    · have h := ratio_u_sq ε
      cases ε <;> norm_num [radicand,FunctionField.firstPolynomial,FunctionField.secondPolynomial,
        leading,constant] at h ⊢
      all_goals norm_num only [map_ofNat] at h ⊢
      all_goals linear_combination h
    · change (ratio ε 2)^2=Polynomial.aeval (ratio ε 0) (4*Polynomial.X^2+45)
      simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using ratio_w_sq ε)

@[simp] theorem affineToChart_m (ε : Bool) : affineToChart ε (Affine.m ε)=ratio ε 0 :=
  DoubleSquareCover.lift_parameter _ _ _ _
@[simp] theorem affineToChart_u (ε : Bool) : affineToChart ε (Affine.u ε)=ratio ε 1 :=
  DoubleSquareCover.lift_root _ _ _ _ 0
@[simp] theorem affineToChart_w (ε : Bool) : affineToChart ε (Affine.w ε)=ratio ε 2 :=
  DoubleSquareCover.lift_root _ _ _ _ 1

theorem chartToAffine_comp (ε : Bool) :
    (chartToAffine ε).comp (affineToChart ε)=AlgHom.id ℚ (Affine.CoordinateRing ε) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change chartToAffine ε (affineToChart ε (Affine.m ε))=Affine.m ε
    rw [affineToChart_m,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (Affine.u ε))=Affine.u ε
    rw [affineToChart_u,chartToAffine_ratio]
    rfl
  · change chartToAffine ε (affineToChart ε (Affine.w ε))=Affine.w ε
    rw [affineToChart_w,chartToAffine_ratio]
    rfl

theorem affineToChart_comp (ε : Bool) :
    (affineToChart ε).comp (chartToAffine ε)=AlgHom.id ℚ (ChartRing ε) := by
  apply AlgHom.coe_ringHom_injective
  apply chartRingHom_ext ε
  intro i
  fin_cases i <;> simp [ratio_self]

def zChartRingEquiv (ε : Bool) : ChartRing ε ≃ₐ[ℚ] Affine.CoordinateRing ε :=
  AlgEquiv.ofAlgHom (chartToAffine ε) (affineToChart ε) (chartToAffine_comp ε) (affineToChart_comp ε)

def zOpen (ε : Bool) : (scheme ε).Opens := Proj.basicOpen (grading ε) (z ε)

def zGammaIso (ε : Bool) : CommRingCat.of (Affine.CoordinateRing ε) ≅ Γ((scheme ε),(zOpen ε)) :=
  (zChartRingEquiv ε).symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway (grading ε) (z ε) (coordinate_degree ε 3) (by decide : 0<1)

def zSectionsRingEquiv (ε : Bool) : ↥Γ((scheme ε),(zOpen ε)) ≃+* Affine.CoordinateRing ε :=
  (zGammaIso ε).symm.commRingCatIsoToRingEquiv

instance zChart_nonempty (ε : Bool) : Nonempty (zOpen ε) := by
  refine ⟨⟨printedPoint ε (ProjValuedPoint.sourcePoint (K:=ℚ)),?_⟩⟩
  apply (ProjValuedPoint.point_mem_basicOpen (grading ε) (printedEvaluation ε)
    (by decide : 0<1) (z ε) (coordinate_degree ε 3) (by simp)
    (by decide : 0<1) (z ε) (coordinate_degree ε 3)).mpr
  simp

theorem zChart_affine (ε : Bool) : IsAffineOpen (zOpen ε) :=
  Proj.isAffineOpen_basicOpen (grading ε) (z ε) (coordinate_degree ε 3) (by decide : 0<1)

end Charts
end
end Z2Z4Rank6.ThirdTwistPairGeometry
