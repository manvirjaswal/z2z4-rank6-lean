import Z2Z4Rank6.SecondSections
import Z2Z4Rank6.PointScaling
import Z2Z4Rank6.BaseCurveArithmetic

/-!
# The three W=4 equations in the proof of Theorem 8.1(b)

The rational fibers, their integral scalings, and the
printed odd-prime denominator tests. The torsion-integrality input is
Silverman, The Arithmetic of Elliptic Curves, VII.3.4, p. 193.
-/
namespace Z2Z4Rank6.SecondW4
noncomputable section
open SecondFamily Common.WeierstrassCoordinates

instance fiber_elliptic : (F (4 : ℚ)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, F_discriminant, U_sq_sub_fourV_sq]
  norm_num [V, lambda]

instance qA_fiber_elliptic : (twistedF (4 : ℚ) (qA 4)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, twistedF_discriminant, F_discriminant, U_sq_sub_fourV_sq]
  norm_num [V, lambda, qA, beta]

instance qH_fiber_elliptic : (twistedF (4 : ℚ) (qH 4)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, twistedF_discriminant, F_discriminant, U_sq_sub_fourV_sq]
  norm_num [V, lambda, qH, beta, gamma]

def integralF : WeierstrassCurve ℤ := ⟨0, 61320178, 0, 191548063527921, 0⟩
def integralQA : WeierstrassCurve ℤ :=
  ⟨0, 8389527940732606, 0, 3585469245239553794740817047809, 0⟩
def integralQH : WeierstrassCurve ℤ :=
  ⟨0, 7705926060596359518, 0, 3024966902891111716582075308921738081, 0⟩

def curveF : WeierstrassCurve ℚ := integralF.map (Int.castRingHom ℚ)
def curveQA : WeierstrassCurve ℚ := integralQA.map (Int.castRingHom ℚ)
def curveQH : WeierstrassCurve ℚ := integralQH.map (Int.castRingHom ℚ)

instance curveF_elliptic : curveF.IsElliptic := by
  constructor
  norm_num [curveF, integralF, WeierstrassCurve.map, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, isUnit_iff_ne_zero]

instance curveQA_elliptic : curveQA.IsElliptic := by
  constructor
  norm_num [curveQA, integralQA, WeierstrassCurve.map, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, isUnit_iff_ne_zero]

instance curveQH_elliptic : curveQH.IsElliptic := by
  constructor
  norm_num [curveQH, integralQH, WeierstrassCurve.map, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, isUnit_iff_ne_zero]

theorem F_eq_long : F (4 : ℚ) = PointScaling.curve (U 4) ((V 4)^2) := by
  ext <;> simp [F, twistedF, PointScaling.curve]

theorem qA_eq_long : twistedF (4 : ℚ) (qA 4) =
    PointScaling.curve (qA 4 * U 4) ((qA 4)^2 * (V 4)^2) := rfl

theorem qH_eq_long : twistedF (4 : ℚ) (qH 4) =
    PointScaling.curve (qH 4 * U 4) ((qH 4)^2 * (V 4)^2) := rfl

theorem scaled_F : PointScaling.curve ((1089 : ℚ)^2 * U 4)
    ((1089 : ℚ)^4 * (V 4)^2) = curveF := by
  ext <;> norm_num [curveF, integralF, PointScaling.curve, U, V, lambda]

theorem scaled_QA : PointScaling.curve ((1185921 : ℚ)^2 * (qA 4 * U 4))
    ((1185921 : ℚ)^4 * ((qA 4)^2 * (V 4)^2)) = curveQA := by
  ext <;> norm_num [curveQA, integralQA, PointScaling.curve, U, V, qA, lambda, beta]

theorem scaled_QH : PointScaling.curve ((190933281 : ℚ)^2 * (qH 4 * U 4))
    ((190933281 : ℚ)^4 * ((qH 4)^2 * (V 4)^2)) = curveQH := by
  ext <;> norm_num [curveQH, integralQH, PointScaling.curve, U, V, qH, lambda, beta, gamma]

def scaleF : (F (4 : ℚ)).toAffine.Point ≃+ RationalPoints curveF :=
  ((PointScaling.pointCongr F_eq_long).trans
    (PointScaling.scaleEquiv _ _ 1089 (by norm_num))).trans
      (PointScaling.pointCongr scaled_F)

def scaleQA : (twistedF (4 : ℚ) (qA 4)).toAffine.Point ≃+ RationalPoints curveQA :=
  ((PointScaling.pointCongr qA_eq_long).trans
    (PointScaling.scaleEquiv _ _ 1185921 (by norm_num))).trans
      (PointScaling.pointCongr scaled_QA)

def scaleQH : (twistedF (4 : ℚ) (qH 4)).toAffine.Point ≃+ RationalPoints curveQH :=
  ((PointScaling.pointCongr qH_eq_long).trans
    (PointScaling.scaleEquiv _ _ 190933281 (by norm_num))).trans
      (PointScaling.pointCongr scaled_QH)

theorem q1_x_coordinate : x1 (4 : ℚ) = 21283118169769/466219936809 := by
  norm_num [x1, mu, lambda]

theorem q6_x_coordinate : x6 (4 : ℚ) =
    11230014732441718248505600/974374006659413003857521 := by
  norm_num [x6, beta, gamma]

def scaledQ1 : RationalPoints curveF :=
  .mk (x := 21283118169769/393129) (y := 145569079189860540850/246491883) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curveF, integralF])

def scaledQ6 : RationalPoints curveQH :=
  .mk (x := 909631193327779178128953600/2164947841)
    (y := -165690551449586976629585009243310981962640/100732858093889) (by
      rw [WeierstrassCurve.Affine.equation_iff]
      norm_num [curveQH, integralQH])

theorem scaleF_Q1 : scaleF (Q1 (4 : ℚ)) = scaledQ1 := by
  apply encode_injective
  simp only [scaleF, AddEquiv.trans_apply, PointScaling.encode_pointCongr,
    PointScaling.encode_scaleEquiv]
  norm_num [Q1, WeierstrassCurve.Affine.Point.mk, encode, scaledQ1, x1, y1, mu, lambda]

theorem scaleQH_Q6 : scaleQH (Q6twist (4 : ℚ)) = scaledQ6 := by
  apply encode_injective
  simp only [scaleQH, AddEquiv.trans_apply, PointScaling.encode_pointCongr,
    PointScaling.encode_scaleEquiv]
  norm_num [Q6twist, WeierstrassCurve.Affine.Point.mk, encode, scaledQ6,
    x6, y6, f6, beta, gamma, lambda]

theorem scaledQ1_x_denominator :
    (21283118169769/393129 : ℚ).den = 3^2 * 11^2 * 19^2 := by norm_num

theorem scaledQ6_x_denominator : 7 ∣ (909631193327779178128953600/2164947841 : ℚ).den := by
  norm_num

theorem q1_infinite_order (hOdd : OddPrimeTorsionIntegrality) :
    ¬IsOfFinAddOrder (Q1 (4 : ℚ)) := by
  intro h
  have hs : IsOfFinAddOrder scaledQ1 := by
    rw [←scaleF_Q1]
    exact scaleF.toAddMonoidHom.isOfFinAddOrder h
  exact (hOdd curveF inferInstance ⟨integralF, rfl⟩ 19 (by decide) (by decide)
    _ _ _ hs) (by norm_num)

theorem q6_infinite_order (hOdd : OddPrimeTorsionIntegrality) :
    ¬IsOfFinAddOrder (Q6twist (4 : ℚ)) := by
  intro h
  have hs : IsOfFinAddOrder scaledQ6 := by
    rw [←scaleQH_Q6]
    exact scaleQH.toAddMonoidHom.isOfFinAddOrder h
  exact (hOdd curveQH inferInstance ⟨integralQH, rfl⟩ 7 (by decide) (by decide)
    _ _ _ hs) scaledQ6_x_denominator

end
end Z2Z4Rank6.SecondW4
