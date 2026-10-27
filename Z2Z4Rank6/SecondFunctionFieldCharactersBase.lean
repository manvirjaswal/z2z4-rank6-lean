import Z2Z4Rank6.SecondFunctionFieldCoordinates
import Z2Z4Rank6.PolynomialWeierstrassSpecialization
import Z2Z4Rank6.PointScaling

/-! The six printed sections before adjoining square roots, as
points on four quadratic twists over Q(W). Polynomial coordinates give
specialization homomorphisms at every smooth rational fiber. -/

namespace Z2Z4Rank6.SecondFunctionField.CharactersBase
noncomputable section
open Polynomial SecondFamily Common.WeierstrassCoordinates
open SecondFunctionFieldLocal
set_option maxHeartbeats 1000000
local instance : Algebra ℚ Base := DivisionRing.toRatAlgebra

theorem polynomialMap_eq_aeval (p : ℚ[X]) :
    PolynomialWeierstrassSpecialization.polynomialMap p=aeval (RatFunc.X : Base) p := by
  have he : PolynomialWeierstrassSpecialization.polynomialMap=
      (aeval (RatFunc.X : Base)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact RingHom.ext_rat _ _
    · simp [PolynomialWeierstrassSpecialization.polynomialMap,RatFunc.algebraMap_X]
  exact RingHom.congr_fun he p


abbrev twistFactor {L : Type*} [Field L] (t : L) : Fin 6 → L :=
  ![1,qA t,qA t,t*qB t,t*qB t,qH t]

abbrev curve (j : Fin 6) : WeierstrassCurve Base :=
  twistedF RatFunc.X (twistFactor RatFunc.X j)

theorem map_twistFactor (j : Fin 6) :
    algebraMap Base K (twistFactor RatFunc.X j)=twistFactor W j := by
  fin_cases j <;> simp [twistFactor,qA,qB,qH,beta,gamma,W,map_ofNat]

theorem twistFactor_W_ne_zero (j : Fin 6) : twistFactor W j ≠ 0 := by
  fin_cases j
  · exact one_ne_zero
  · exact qA_W_ne_zero
  · exact qA_W_ne_zero
  · exact mul_ne_zero W_ne_zero qB_W_ne_zero
  · exact mul_ne_zero W_ne_zero qB_W_ne_zero
  · exact qH_ne_zero_of_qA_qB W qA_W_ne_zero qB_W_ne_zero

theorem twistFactor_ne_zero (j : Fin 6) : twistFactor (RatFunc.X : Base) j ≠ 0 := by
  intro h
  apply twistFactor_W_ne_zero j
  rw [←map_twistFactor,h,map_zero]

instance baseF_elliptic : (F (RatFunc.X : Base)).IsElliptic := by
  have he : (F (RatFunc.X : Base)).map (algebraMap Base K)=F W := by
    ext <;> simp [F,twistedF,U,V,lambda,W,map_ofNat]
  constructor
  rw [isUnit_iff_ne_zero]
  intro h
  apply (F W).isUnit_Δ.ne_zero
  rw [←he,WeierstrassCurve.map_Δ,h,map_zero]

instance curve_elliptic (j : Fin 6) : (curve j).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero,curve,twistedF_discriminant]
  exact mul_ne_zero (pow_ne_zero _ (twistFactor_ne_zero j))
    (F (RatFunc.X : Base)).isUnit_Δ.ne_zero

instance qA_curve_elliptic : (twistedF (RatFunc.X : Base) (qA RatFunc.X)).IsElliptic :=
  curve_elliptic 1
instance qB_curve_elliptic : (twistedF (RatFunc.X : Base) (RatFunc.X*qB RatFunc.X)).IsElliptic :=
  curve_elliptic 3
instance qH_curve_elliptic : (twistedF (RatFunc.X : Base) (qH RatFunc.X)).IsElliptic :=
  curve_elliptic 5

def point : (j : Fin 6) → (curve j).toAffine.Point
  | ⟨0,_⟩ => Q1 RatFunc.X
  | ⟨1,_⟩ => Q2twist RatFunc.X
  | ⟨2,_⟩ => Q3twist RatFunc.X
  | ⟨3,_⟩ => Q4twist RatFunc.X RatFunc.X_ne_zero
  | ⟨4,_⟩ => Q5twist RatFunc.X RatFunc.X_ne_zero
  | ⟨5,_⟩ => Q6twist RatFunc.X
  | ⟨n+6,h⟩ => False.elim (by omega)

def polynomialCurve (j : Fin 6) : WeierstrassCurve ℚ[X] :=
  ⟨0,qDenominator j*uPolynomial,0,(qDenominator j)^2*vPolynomial^2,0⟩

theorem polynomialCurve_generic (j : Fin 6) :
    PolynomialWeierstrassSpecialization.generic (polynomialCurve j)=curve j := by
  have hq : PolynomialWeierstrassSpecialization.polynomialMap (qDenominator j)=
      twistFactor (RatFunc.X : Base) j := by
    rw [polynomialMap_eq_aeval]
    exact qDenominator_eval (RatFunc.X : Base) j
  have hu : PolynomialWeierstrassSpecialization.polynomialMap uPolynomial=U (RatFunc.X : Base) := by
    rw [polynomialMap_eq_aeval]
    exact uPolynomial_eval (RatFunc.X : Base)
  have hv : PolynomialWeierstrassSpecialization.polynomialMap vPolynomial=V (RatFunc.X : Base) := by
    rw [polynomialMap_eq_aeval]
    exact vPolynomial_eval (RatFunc.X : Base)
  ext <;> simp [PolynomialWeierstrassSpecialization.generic,polynomialCurve,
    WeierstrassCurve.map,curve,twistedF,hq,hu,hv]

theorem polynomialCurve_fiber (j : Fin 6) (r : ℚ) :
    PolynomialWeierstrassSpecialization.fiber (polynomialCurve j) r=twistedF r (twistFactor r j) := by
  have eval_eq (p : ℚ[X]) : p.eval r=aeval r p := by simp [Polynomial.aeval_def]
  have hq : (qDenominator j).eval r=twistFactor r j := by
    rw [eval_eq]
    exact qDenominator_eval r j
  have hu : uPolynomial.eval r=U r := by rw [eval_eq]; exact uPolynomial_eval r
  have hv : vPolynomial.eval r=V r := by rw [eval_eq]; exact vPolynomial_eval r
  ext <;> simp [PolynomialWeierstrassSpecialization.fiber,polynomialCurve,
    WeierstrassCurve.map,PolynomialWeierstrassSpecialization.evaluation,twistedF,hq,hu,hv]

theorem encode_point (j : Fin 6) : encode (point j)=
    some (PolynomialWeierstrassSpecialization.polynomialMap (xNumerator j),PolynomialWeierstrassSpecialization.polynomialMap (yNumerator j)) := by
  rw [polynomialMap_eq_aeval,polynomialMap_eq_aeval,xNumerator_eval (RatFunc.X : Base) RatFunc.X_ne_zero j,
    yNumerator_eval (RatFunc.X : Base) RatFunc.X_ne_zero j]
  fin_cases j <;> rfl

theorem exists_specialization (hFormal : FormalGoodReductionHomomorphisms)
    (j : Fin 6) (r : ℚ) [(twistedF r (twistFactor r j)).IsElliptic] :
    ∃ spec : (curve j).toAffine.Point →+ (twistedF r (twistFactor r j)).toAffine.Point,
      ∀ (x y : ℚ[X]) (P : (curve j).toAffine.Point),
        encode P=some (PolynomialWeierstrassSpecialization.polynomialMap x,
          PolynomialWeierstrassSpecialization.polynomialMap y) →
        encode (spec P)=some (x.eval r,y.eval r) := by
  let : (PolynomialWeierstrassSpecialization.generic (polynomialCurve j)).IsElliptic := by
    rw [polynomialCurve_generic]
    infer_instance
  let : (PolynomialWeierstrassSpecialization.fiber (polynomialCurve j) r).IsElliptic := by
    rw [polynomialCurve_fiber]
    infer_instance
  obtain ⟨spec,hspec⟩ := PolynomialWeierstrassSpecialization.exists_specialization hFormal (polynomialCurve j) r
  let e := PointScaling.pointCongr (polynomialCurve_generic j).symm
  let f := PointScaling.pointCongr (polynomialCurve_fiber j r)
  refine ⟨f.toAddMonoidHom.comp (spec.comp e.toAddMonoidHom),?_⟩
  intro x y P henc
  have he : encode (e P)=
      some (PolynomialWeierstrassSpecialization.polynomialMap x,
        PolynomialWeierstrassSpecialization.polynomialMap y) := by
    rw [PointScaling.encode_pointCongr,henc]
  obtain ⟨hN,hshape⟩ : ∃ hN, e P=
      WeierstrassCurve.Affine.Point.some (PolynomialWeierstrassSpecialization.polynomialMap x)
        (PolynomialWeierstrassSpecialization.polynomialMap y) hN := by
    cases hp : e P with
    | zero => simp only [hp,encode] at he; cases he
    | some a b hN =>
      rw [hp] at he
      obtain ⟨ha,hb⟩ := Prod.mk.inj (Option.some.inj he)
      subst a
      subst b
      exact ⟨hN,rfl⟩
  change encode (f (spec (e P)))=_
  rw [PointScaling.encode_pointCongr,hshape]
  exact hspec _ _ hN

end
end Z2Z4Rank6.SecondFunctionField.CharactersBase
