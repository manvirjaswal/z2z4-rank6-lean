import Z2Z4Rank6.SecondFunctionFieldCharactersBase
import Z2Z4Rank6.QuadraticRatFuncEquiv
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# The generic reciprocal isomorphism of the second family

The printed substitution W -> lambda^2/W is an involution of Q(W).
Applying it to point coordinates and then scaling by iotaScale(W)
gives the additive equivalence F^qA(Q(W)) -> F^(W qB)(Q(W)).
It carries the two printed sections Q2,Q3 exactly to Q4,Q5.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily Common.WeierstrassCoordinates

abbrev GenericField := RatFunc ℚ
local instance : Algebra ℚ GenericField := RatFunc.instAlgebraOfPolynomial ℚ ℚ
local instance : DecidableEq GenericField := Classical.decEq _

theorem reciprocal_transcendental :
    Transcendental ℚ (sigma (RatFunc.X : GenericField)) := by
  intro h
  apply RatFunc.transcendental_X (K := ℚ)
  have ha := (isAlgebraic_algebraMap (R := ℚ) (A := GenericField)
    ((361/1089 : ℚ)^2)).mul h.inv
  have he : algebraMap ℚ GenericField ((361/1089 : ℚ)^2) /
      sigma (RatFunc.X : GenericField) = RatFunc.X := by
    norm_num [sigma, lambda]
  rw [←div_eq_mul_inv, he] at ha
  exact ha

def reciprocalFieldMap : GenericField →ₐ[ℚ] GenericField :=
  (QuadraticRatFuncEquiv.baseEmbedding (sigma (RatFunc.X : GenericField))
    reciprocal_transcendental).toRatAlgHom

@[simp] theorem reciprocalFieldMap_X :
    reciprocalFieldMap (RatFunc.X : GenericField) = sigma RatFunc.X := by
  change QuadraticRatFuncEquiv.baseEmbedding (sigma (RatFunc.X : GenericField))
    reciprocal_transcendental RatFunc.X = _
  exact QuadraticRatFuncEquiv.baseEmbedding_X _ reciprocal_transcendental

theorem reciprocalFieldMap_square :
    reciprocalFieldMap.comp reciprocalFieldMap = AlgHom.id ℚ GenericField := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | monomial d a =>
    change reciprocalFieldMap (reciprocalFieldMap
      (algebraMap (Polynomial ℚ) GenericField (Polynomial.monomial d a))) = _
    rw [RatFunc.algebraMap_monomial]
    have ha : RatFunc.C a = algebraMap ℚ GenericField a := by
      exact (congrArg (fun f : ℚ →+* GenericField => f a) RatFunc.algebraMap_eq_C).symm
    rw [ha]
    simp only [map_mul, map_pow, AlgHom.commutes, reciprocalFieldMap_X]
    simp [sigma, lambda, map_div₀, map_ofNat]

theorem reciprocalFieldMap_involutive (z : GenericField) :
    reciprocalFieldMap (reciprocalFieldMap z) = z :=
  DFunLike.congr_fun reciprocalFieldMap_square z

def reciprocalFieldEquiv : GenericField ≃ₐ[ℚ] GenericField :=
  AlgEquiv.ofAlgHom reciprocalFieldMap reciprocalFieldMap
    reciprocalFieldMap_square reciprocalFieldMap_square

theorem map_twice (W : WeierstrassCurve GenericField) :
    (W.map reciprocalFieldMap.toRingHom).map reciprocalFieldMap.toRingHom = W := by
  ext <;> simp only [WeierstrassCurve.map, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, reciprocalFieldMap_involutive]

/-- Applying the field involution to every coordinate is an
additive equivalence to the coefficient-transformed equation. -/
def fieldPointEquiv (W : WeierstrassCurve GenericField) :
    W.toAffine.Point ≃+ (W.map reciprocalFieldMap.toRingHom).toAffine.Point where
  toFun := fieldPointMap reciprocalFieldMap.toRingHom W
  invFun P := PointScaling.pointCongr (map_twice W)
    (fieldPointMap reciprocalFieldMap.toRingHom (W.map reciprocalFieldMap.toRingHom) P)
  left_inv P := by
    apply encode_injective
    rw [PointScaling.encode_pointCongr, encode_fieldPointMap, encode_fieldPointMap]
    cases P with
    | zero => rfl
    | some x y h =>
      simp only [encode, Option.map_some, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, reciprocalFieldMap_involutive]
  right_inv P := by
    apply encode_injective
    rw [encode_fieldPointMap, PointScaling.encode_pointCongr, encode_fieldPointMap]
    cases P with
    | zero => rfl
    | some x y h =>
      simp only [encode, Option.map_some, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, reciprocalFieldMap_involutive]
  map_add' := (fieldPointMap reciprocalFieldMap.toRingHom W).map_add

theorem encode_fieldPointEquiv (W : WeierstrassCurve GenericField)
    (P : W.toAffine.Point) :
    encode (fieldPointEquiv W P) =
      (encode P).map (fun xy => (reciprocalFieldMap xy.1, reciprocalFieldMap xy.2)) :=
  encode_fieldPointMap _ _ _

theorem mapped_qA_curve :
    (twistedF (RatFunc.X : GenericField) (qA RatFunc.X)).map reciprocalFieldMap.toRingHom =
      twistedF (sigma RatFunc.X) (qA (sigma RatFunc.X)) := by
  ext <;> simp [WeierstrassCurve.map, twistedF, qA, U, V, lambda, beta,
    reciprocalFieldMap_X, map_ofNat, sigma]

theorem scaled_generic_reciprocal :
    PointScaling.curve ((iotaScale (RatFunc.X : GenericField))^2*
        (qA (sigma RatFunc.X)*U (sigma RatFunc.X)))
      ((iotaScale (RatFunc.X : GenericField))^4*
        ((qA (sigma RatFunc.X))^2*(V (sigma RatFunc.X))^2)) =
      twistedF RatFunc.X (RatFunc.X*qB RatFunc.X) := by
  ext <;> simp only [PointScaling.curve, twistedF]
  · rw [qA_involution _ RatFunc.X_ne_zero, U_involution _ RatFunc.X_ne_zero]
    unfold iotaScale
    field_simp [RatFunc.X_ne_zero, lambda_ne_zero]
  · rw [qA_involution _ RatFunc.X_ne_zero, V_involution _ RatFunc.X_ne_zero]
    unfold iotaScale
    field_simp [RatFunc.X_ne_zero, lambda_ne_zero]

theorem generic_qA_sigma_long :
    twistedF (sigma (RatFunc.X : GenericField)) (qA (sigma RatFunc.X)) =
      PointScaling.curve (qA (sigma RatFunc.X)*U (sigma RatFunc.X))
        ((qA (sigma RatFunc.X))^2*(V (sigma RatFunc.X))^2) := rfl

theorem generic_iotaScale_ne_zero : iotaScale (RatFunc.X : GenericField) ≠ 0 := by
  exact div_ne_zero (pow_ne_zero _ RatFunc.X_ne_zero) lambda_ne_zero

def genericIota :
    (twistedF (RatFunc.X : GenericField) (qA RatFunc.X)).toAffine.Point ≃+
      (twistedF (RatFunc.X : GenericField) (RatFunc.X*qB RatFunc.X)).toAffine.Point :=
  ((((fieldPointEquiv (twistedF RatFunc.X (qA RatFunc.X))).trans
    (PointScaling.pointCongr mapped_qA_curve)).trans
    (PointScaling.pointCongr generic_qA_sigma_long)).trans
    (PointScaling.scaleEquiv _ _ (iotaScale RatFunc.X) generic_iotaScale_ne_zero)).trans
        (PointScaling.pointCongr scaled_generic_reciprocal)

theorem genericIota_Q2 : genericIota (Q2twist (RatFunc.X : GenericField)) =
    Q4twist (RatFunc.X : GenericField) (RatFunc.X_ne_zero (K := ℚ)) := by
  apply encode_injective
  simp only [genericIota, AddEquiv.trans_apply]
  rw [PointScaling.encode_pointCongr, PointScaling.encode_scaleEquiv,
    PointScaling.encode_pointCongr, PointScaling.encode_pointCongr, encode_fieldPointEquiv]
  simp [Q2twist, Q4twist, WeierstrassCurve.Affine.Point.mk, encode,
    x2, y2, f2, x4, y4, lambda, reciprocalFieldMap_X, map_ofNat]

theorem genericIota_Q3 : genericIota (Q3twist (RatFunc.X : GenericField)) =
    Q5twist (RatFunc.X : GenericField) (RatFunc.X_ne_zero (K := ℚ)) := by
  apply encode_injective
  simp only [genericIota, AddEquiv.trans_apply]
  rw [PointScaling.encode_pointCongr, PointScaling.encode_scaleEquiv,
    PointScaling.encode_pointCongr, PointScaling.encode_pointCongr, encode_fieldPointEquiv]
  simp [Q3twist, Q5twist, WeierstrassCurve.Affine.Point.mk, encode,
    x3, y3, x5, y5, beta, reciprocalFieldMap_X, map_ofNat]

end
end Z2Z4Rank6.SecondW4
