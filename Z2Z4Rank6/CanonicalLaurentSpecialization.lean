import Z2Z4Rank6.PointMap
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

/-!
# Canonical reduction of Laurent-series points

For an integral Weierstrass model with smooth constant fiber, an affine
point with power-series coordinates reduces by taking constant coefficients.
A point with nonintegral affine coordinates reduces to infinity. This is
the projective reduction described by Silverman, The Arithmetic of
Elliptic Curves, second edition, VII.2, pp. 187–188. The function is defined here explicitly.
-/

namespace Z2Z4Rank6.CanonicalLaurentSpecialization
open scoped Classical
noncomputable section

variable {F : Type} [Field F]

abbrev PS := PowerSeries F
abbrev LS := LaurentSeries F

def IsIntegral (z : LS (F:=F)) : Prop :=
  ∃ a : PS (F:=F), algebraMap (PS (F:=F)) (LS (F:=F)) a=z

def integralPart (z : LS (F:=F)) : PS (F:=F) :=
  if h : IsIntegral z then h.choose else 0

theorem integralPart_spec (z : LS (F:=F)) (h : IsIntegral z) :
    algebraMap (PS (F:=F)) (LS (F:=F)) (integralPart z)=z := by
  classical
  simpa only [integralPart,dite_eq_left h] using h.choose_spec

@[simp] theorem integralPart_algebraMap (a : PS (F:=F)) :
    integralPart (algebraMap (PS (F:=F)) (LS (F:=F)) a)=a := by
  apply IsFractionRing.injective (PS (F:=F)) (LS (F:=F))
  exact integralPart_spec _ ⟨a,rfl⟩

abbrev laurentCurve (W : WeierstrassCurve (PS (F:=F))) : WeierstrassCurve (LS (F:=F)) :=
  W.map (algebraMap (PS (F:=F)) (LS (F:=F)))

abbrev constantCurve (W : WeierstrassCurve (PS (F:=F))) : WeierstrassCurve F :=
  W.map (PowerSeries.constantCoeff : PS (F:=F) →+* F)

theorem constant_equation (W : WeierstrassCurve (PS (F:=F)))
    (x y : LS (F:=F)) (hx : IsIntegral x) (hy : IsIntegral y)
    (h : (laurentCurve W).toAffine.Equation x y) :
    (constantCurve W).toAffine.Equation
      (PowerSeries.constantCoeff (integralPart x))
      (PowerSeries.constantCoeff (integralPart y)) := by
  have hPS : W.toAffine.Equation (integralPart x) (integralPart y) := by
    apply (W.toAffine.map_equation
      (IsFractionRing.injective (PS (F:=F)) (LS (F:=F))) _ _).mp
    simpa only [integralPart_spec x hx,integralPart_spec y hy] using h
  exact hPS.map (PowerSeries.constantCoeff : PS (F:=F) →+* F)

def reduce (W : WeierstrassCurve (PS (F:=F))) [(constantCurve W).IsElliptic] :
    (laurentCurve W).toAffine.Point → (constantCurve W).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hi : IsIntegral x ∧ IsIntegral y then
      .some (PowerSeries.constantCoeff (integralPart x))
        (PowerSeries.constantCoeff (integralPart y))
        ((constantCurve W).toAffine.equation_iff_nonsingular.mp
          (constant_equation W x y hi.1 hi.2 h.1))
    else .zero

@[simp] theorem reduce_zero (W : WeierstrassCurve (PS (F:=F)))
    [(constantCurve W).IsElliptic] : reduce W 0=0 := rfl

theorem reduce_nonintegral (W : WeierstrassCurve (PS (F:=F)))
    [(constantCurve W).IsElliptic] (x y : LS (F:=F))
    (h : (laurentCurve W).toAffine.Nonsingular x y)
    (hi : ¬(IsIntegral x ∧ IsIntegral y)) : reduce W (.some x y h)=0 := by
  classical
  simp only [reduce,dite_eq_right hi]
  rfl

theorem encode_reduce_integral (W : WeierstrassCurve (PS (F:=F)))
    [(constantCurve W).IsElliptic] (x y : PS (F:=F))
    (h : (laurentCurve W).toAffine.Nonsingular
      (algebraMap (PS (F:=F)) (LS (F:=F)) x)
      (algebraMap (PS (F:=F)) (LS (F:=F)) y)) :
    Common.WeierstrassCoordinates.encode (reduce W (.some _ _ h))=
      some (PowerSeries.constantCoeff x,PowerSeries.constantCoeff y) := by
  classical
  simp only [reduce,dite_eq_left (show IsIntegral (algebraMap (PS (F:=F)) (LS (F:=F)) x) ∧
    IsIntegral (algebraMap (PS (F:=F)) (LS (F:=F)) y) from ⟨⟨x,rfl⟩,⟨y,rfl⟩⟩),
    integralPart_algebraMap,Common.WeierstrassCoordinates.encode]

end
end Z2Z4Rank6.CanonicalLaurentSpecialization
