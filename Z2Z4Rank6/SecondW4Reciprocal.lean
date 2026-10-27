module

public import Z2Z4Rank6.SecondW4Descent

@[expose] public section

/-!
# The reciprocal specialization in the printed iota argument

At W=lambda^2/4 the printed involution has sigma(W)=4. Its
coordinate scaling carries Q2(4),Q3(4) to Q4(W),Q5(W), so the latter
two points are independent as well.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily Common.WeierstrassCoordinates

def reciprocalParameter : ℚ := (lambda : ℚ)^2/4

theorem reciprocal_ne_zero : reciprocalParameter ≠ 0 := by
  norm_num [reciprocalParameter, lambda]

theorem sigma_reciprocal : sigma reciprocalParameter = 4 := by
  norm_num [sigma, reciprocalParameter, lambda]

instance reciprocal_fiber_elliptic :
    (twistedF reciprocalParameter (reciprocalParameter*qB reciprocalParameter)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, twistedF_discriminant, F_discriminant, U_sq_sub_fourV_sq]
  norm_num [V, qB, lambda, beta, gamma, reciprocalParameter]

theorem scaled_reciprocal :
    PointScaling.curve ((iotaScale reciprocalParameter)^2*(qA (4 : ℚ)*U 4))
      ((iotaScale reciprocalParameter)^4*((qA (4 : ℚ))^2*(V 4)^2)) =
      twistedF reciprocalParameter (reciprocalParameter*qB reciprocalParameter) := by
  ext <;> norm_num [PointScaling.curve, twistedF, iotaScale,
    reciprocalParameter, qA, qB, U, V, lambda, beta, gamma]

def reciprocalScale : (twistedF (4 : ℚ) (qA 4)).toAffine.Point ≃+
    (twistedF reciprocalParameter (reciprocalParameter*qB reciprocalParameter)).toAffine.Point :=
  ((PointScaling.pointCongr qA_eq_long).trans
    (PointScaling.scaleEquiv _ _ (iotaScale reciprocalParameter)
      (by norm_num [iotaScale, reciprocalParameter, lambda]))).trans
        (PointScaling.pointCongr scaled_reciprocal)

theorem reciprocalScale_Q2 : reciprocalScale (Q2twist (4 : ℚ)) =
    Q4twist reciprocalParameter reciprocal_ne_zero := by
  apply encode_injective
  simp only [reciprocalScale, AddEquiv.trans_apply, PointScaling.encode_pointCongr,
    PointScaling.encode_scaleEquiv]
  simp only [Q2twist, Q4twist, WeierstrassCurve.Affine.Point.mk, encode,
    x4, y4, sigma_reciprocal, Option.map_some]

theorem reciprocalScale_Q3 : reciprocalScale (Q3twist (4 : ℚ)) =
    Q5twist reciprocalParameter reciprocal_ne_zero := by
  apply encode_injective
  simp only [reciprocalScale, AddEquiv.trans_apply, PointScaling.encode_pointCongr,
    PointScaling.encode_scaleEquiv]
  simp only [Q3twist, Q5twist, WeierstrassCurve.Affine.Point.mk, encode,
    x5, y5, sigma_reciprocal, Option.map_some]

theorem reciprocal_points_independent
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) :
    LinearIndependent ℤ ![Q4twist reciprocalParameter reciprocal_ne_zero,
      Q5twist reciprocalParameter reciprocal_ne_zero] := by
  have he : (fun i : Fin 2 => reciprocalScale (qAPoints i)) =
      ![Q4twist reciprocalParameter reciprocal_ne_zero,
        Q5twist reciprocalParameter reciprocal_ne_zero] := by
    funext i
    fin_cases i
    · exact reciprocalScale_Q2
    · exact reciprocalScale_Q3
  rw [←he]
  exact (qA_points_independent hOdd hReduction hDescent).map'
    reciprocalScale.toIntLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot.mpr reciprocalScale.injective)

end
end Z2Z4Rank6.SecondW4
