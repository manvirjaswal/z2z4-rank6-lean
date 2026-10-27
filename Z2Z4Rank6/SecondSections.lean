import Z2Z4Rank6.SecondFamily
import Mathlib.GroupTheory.OrderOfElement
import Common.Elliptic.WeierstrassCoordinates

/-!
# The second family's printed sections

The four twist-section factorizations preceding Theorem 8.1 of M. Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117. The y signs are chosen explicitly from
the printed square factors; the paper fixes only the x coordinates here.
-/

namespace Z2Z4Rank6.SecondFamily

variable {K : Type*} [Field K] [CharZero K]

def f2 (W : K) : K := W^2-(648517/1185921)*W+3467044/1291467969
def f6 (W : K) : K := W^2-(14138244652530322/796818233864961)*W+lambda^2

def x1 (W : K) : K := mu^(-2 : ℤ)*(W-lambda^2)^2
def x2 (W : K) : K := (1015/1089)^2*(W-1)*(W-lambda^2)
def x3 (W : K) : K := (928/1089)^2*(W-1)*(W-beta)
def x6 (W : K) : K := (240/289)^2*(W-beta)^2*(W-gamma)^2

def y1 (W : K) : K := ((33/19)*(1450/361))*(W+lambda)*(W-lambda^2)^2
def y2 (W : K) : K := (29*(1015/1089))*(W-1)*(W-lambda^2)*f2 W
def y3 (W : K) : K := (29*(928/1089))*(W-1)*(W-beta)^2*(W-625/1089)
def y6 (W : K) : K := ((240/289)*(161/289)^2)*(W-beta)^2*(W-gamma)^2*f6 W

/-- The first printed quadratic factor at x(Q₁). -/
theorem x1_factor (W : K) :
    (x1 W)^2+U W*x1 W+(V W)^2=
      (2102500/130321)*(W+lambda)^2*(W-lambda^2)^2 := by
  norm_num [x1, U, V, mu, lambda]
  ring

/-- The second printed quadratic factor at x(Q₂). -/
theorem x2_factor (W : K) :
    (x2 W)^2+qA W*U W*x2 W+(qA W)^2*(V W)^2=
      841*(W-1)*(W-lambda^2)*(f2 W)^2 := by
  norm_num [x2, U, V, qA, lambda, beta, f2]
  ring

/-- The third printed quadratic factor at x(Q₃). -/
theorem x3_factor (W : K) :
    (x3 W)^2+qA W*U W*x3 W+(qA W)^2*(V W)^2=
      841*(W-1)*(W-beta)^3*(W-625/1089)^2 := by
  norm_num [x3, U, V, qA, lambda, beta]
  ring

/-- The fourth printed quadratic factor at x(Q₆). -/
theorem x6_factor (W : K) :
    (x6 W)^2+qH W*U W*x6 W+(qH W)^2*(V W)^2=
      (671898241/6975757441)*(W-beta)^2*(W-gamma)^2*(f6 W)^2 := by
  norm_num [x6, U, V, qH, lambda, beta, gamma, f6]
  ring

theorem Q1_equation (W : K) : (y1 W)^2=x1 W*((x1 W)^2+U W*x1 W+(V W)^2) := by
  rw [x1_factor]
  norm_num [x1, y1, mu]
  ring

theorem Q2_equation (W : K) :
    (y2 W)^2=x2 W*((x2 W)^2+qA W*U W*x2 W+(qA W)^2*(V W)^2) := by
  rw [x2_factor]
  norm_num [x2, y2]
  ring

theorem Q3_equation (W : K) :
    (y3 W)^2=x3 W*((x3 W)^2+qA W*U W*x3 W+(qA W)^2*(V W)^2) := by
  rw [x3_factor]
  norm_num [x3, y3]
  ring

theorem Q6_equation (W : K) :
    (y6 W)^2=x6 W*((x6 W)^2+qH W*U W*x6 W+(qH W)^2*(V W)^2) := by
  rw [x6_factor]
  norm_num [x6, y6]
  ring

def Q1 (W : K) [(F W).IsElliptic] : (F W).toAffine.Point :=
  .mk ((F_equation_iff W _ _).2 (Q1_equation W))

def Q2twist (W : K) [(twistedF W (qA W)).IsElliptic] :
    (twistedF W (qA W)).toAffine.Point :=
  .mk ((twistedF_equation_iff W _ _ _).2 (Q2_equation W))

def Q3twist (W : K) [(twistedF W (qA W)).IsElliptic] :
    (twistedF W (qA W)).toAffine.Point :=
  .mk ((twistedF_equation_iff W _ _ _).2 (Q3_equation W))

def Q6twist (W : K) [(twistedF W (qH W)).IsElliptic] :
    (twistedF W (qH W)).toAffine.Point :=
  .mk ((twistedF_equation_iff W _ _ _).2 (Q6_equation W))

def x4 (W : K) : K := iotaScale W^2*x2 (sigma W)
def y4 (W : K) : K := iotaScale W^3*y2 (sigma W)
def x5 (W : K) : K := iotaScale W^2*x3 (sigma W)
def y5 (W : K) : K := iotaScale W^3*y3 (sigma W)

theorem Q4_equation (W : K) (hW : W ≠ 0) :
    (y4 W)^2=x4 W*((x4 W)^2+(W*qB W)*U W*x4 W+(W*qB W)^2*(V W)^2) :=
  iota_equation W _ _ hW (Q2_equation (sigma W))

theorem Q5_equation (W : K) (hW : W ≠ 0) :
    (y5 W)^2=x5 W*((x5 W)^2+(W*qB W)*U W*x5 W+(W*qB W)^2*(V W)^2) :=
  iota_equation W _ _ hW (Q3_equation (sigma W))

def Q4twist (W : K) (hW : W ≠ 0) [(twistedF W (W*qB W)).IsElliptic] :
    (twistedF W (W*qB W)).toAffine.Point :=
  .mk ((twistedF_equation_iff W _ _ _).2 (Q4_equation W hW))

def Q5twist (W : K) (hW : W ≠ 0) [(twistedF W (W*qB W)).IsElliptic] :
    (twistedF W (W*qB W)).toAffine.Point :=
  .mk ((twistedF_equation_iff W _ _ _).2 (Q5_equation W hW))

omit [CharZero K] in
/-- On G₂ this is the printed square root of W q_B. -/
theorem G2Point.WqB_square (P : G2Point K) : (P.s1*P.s3)^2=P.W*qB P.W := by
  rw [mul_pow, P.s1_sq, P.s3_sq]

def G2Point.untwistedX2 (P : G2Point K) : K := x2 P.W/qA P.W
def G2Point.untwistedY2 (P : G2Point K) : K := y2 P.W/(qA P.W*P.s2)
def G2Point.untwistedX3 (P : G2Point K) : K := x3 P.W/qA P.W
def G2Point.untwistedY3 (P : G2Point K) : K := y3 P.W/(qA P.W*P.s2)
def G2Point.untwistedX4 (P : G2Point K) : K := x4 P.W/(P.W*qB P.W)
def G2Point.untwistedY4 (P : G2Point K) : K := y4 P.W/(P.W*qB P.W*(P.s1*P.s3))
def G2Point.untwistedX5 (P : G2Point K) : K := x5 P.W/(P.W*qB P.W)
def G2Point.untwistedY5 (P : G2Point K) : K := y5 P.W/(P.W*qB P.W*(P.s1*P.s3))
def G2Point.untwistedX6 (P : G2Point K) : K := x6 P.W/qH P.W
def G2Point.untwistedY6 (P : G2Point K) : K :=
  y6 P.W/(qH P.W*(1089*P.s2*P.s3/4669))

/-- The six displayed affine abscissae after untwisting on G₂. -/
def G2Point.sixX (P : G2Point K) : Fin 6 → K :=
  ![x1 P.W,P.untwistedX2,P.untwistedX3,P.untwistedX4,P.untwistedX5,P.untwistedX6]

/-- The six signed affine ordinates after untwisting on G₂. -/
def G2Point.sixY (P : G2Point K) : Fin 6 → K :=
  ![y1 P.W,P.untwistedY2,P.untwistedY3,P.untwistedY4,P.untwistedY5,P.untwistedY6]

theorem G2Point.Q2_untwisted_equation (P : G2Point K) (hA : qA P.W ≠ 0) :
    (F P.W).toAffine.Equation P.untwistedX2 P.untwistedY2 := by
  apply (F_equation_iff _ _ _).2
  exact untwist_equation _ _ _ _ _ _ hA P.s2_sq (Q2_equation P.W)

theorem G2Point.Q3_untwisted_equation (P : G2Point K) (hA : qA P.W ≠ 0) :
    (F P.W).toAffine.Equation P.untwistedX3 P.untwistedY3 := by
  apply (F_equation_iff _ _ _).2
  exact untwist_equation _ _ _ _ _ _ hA P.s2_sq (Q3_equation P.W)

theorem G2Point.Q4_untwisted_equation (P : G2Point K)
    (hW : P.W ≠ 0) (hB : qB P.W ≠ 0) :
    (F P.W).toAffine.Equation P.untwistedX4 P.untwistedY4 := by
  apply (F_equation_iff _ _ _).2
  exact untwist_equation _ _ _ _ _ _ (mul_ne_zero hW hB) P.WqB_square
    (Q4_equation P.W hW)

theorem G2Point.Q5_untwisted_equation (P : G2Point K)
    (hW : P.W ≠ 0) (hB : qB P.W ≠ 0) :
    (F P.W).toAffine.Equation P.untwistedX5 P.untwistedY5 := by
  apply (F_equation_iff _ _ _).2
  exact untwist_equation _ _ _ _ _ _ (mul_ne_zero hW hB) P.WqB_square
    (Q5_equation P.W hW)

theorem G2Point.Q6_untwisted_equation (P : G2Point K) (hH : qH P.W ≠ 0) :
    (F P.W).toAffine.Equation P.untwistedX6 P.untwistedY6 := by
  apply (F_equation_iff _ _ _).2
  exact untwist_equation _ _ _ _ _ _ hH P.qH_square (Q6_equation P.W)

/-- The six points of the elliptic fiber on the affine chart where
the displayed untwisting formulas have no poles. -/
def G2Point.sixPoints (P : G2Point K) (hW : P.W ≠ 0)
    (hA : qA P.W ≠ 0) (hB : qB P.W ≠ 0)
    [(F P.W).IsElliptic] : Fin 6 → (F P.W).toAffine.Point :=
  ![Q1 P.W,
    .mk (P.Q2_untwisted_equation hA),
    .mk (P.Q3_untwisted_equation hA),
    .mk (P.Q4_untwisted_equation hW hB),
    .mk (P.Q5_untwisted_equation hW hB),
    .mk (P.Q6_untwisted_equation (qH_ne_zero_of_qA_qB _ hA hB))]

theorem G2Point.six_affine_equations (P : G2Point K) (hW : P.W ≠ 0)
    (hA : qA P.W ≠ 0) (hB : qB P.W ≠ 0) (j : Fin 6) :
    (F P.W).toAffine.Equation (P.sixX j) (P.sixY j) := by
  fin_cases j
  · exact (F_equation_iff _ _ _).2 (Q1_equation P.W)
  · exact P.Q2_untwisted_equation hA
  · exact P.Q3_untwisted_equation hA
  · exact P.Q4_untwisted_equation hW hB
  · exact P.Q5_untwisted_equation hW hB
  · exact P.Q6_untwisted_equation (qH_ne_zero_of_qA_qB _ hA hB)

theorem G2Point.sixPoints_eq_mk (P : G2Point K) (hW : P.W ≠ 0)
    (hA : qA P.W ≠ 0) (hB : qB P.W ≠ 0) [(F P.W).IsElliptic] (j : Fin 6) :
    P.sixPoints hW hA hB j = .mk (P.six_affine_equations hW hA hB j) := by
  fin_cases j <;> rfl

theorem G2Point.encode_sixPoints (P : G2Point K) (hW : P.W ≠ 0)
    (hA : qA P.W ≠ 0) (hB : qB P.W ≠ 0) [(F P.W).IsElliptic] (j : Fin 6) :
    Common.WeierstrassCoordinates.encode (P.sixPoints hW hA hB j)=
      some (P.sixX j,P.sixY j) := by
  fin_cases j <;> rfl

omit [CharZero K] in
theorem V_ne_zero_of_elliptic (W : K) [(F W).IsElliptic] : V W ≠ 0 := by
  intro hV
  apply (F W).isUnit_Δ.ne_zero
  rw [F_discriminant, hV]
  ring

omit [CharZero K] in
theorem W_add_lambda_ne_zero_of_elliptic (W : K) [(F W).IsElliptic] :
    W+lambda ≠ 0 := by
  intro h
  apply (F W).isUnit_Δ.ne_zero
  rw [F_discriminant, U_sq_sub_fourV_sq, h]
  ring

/-- The printed order-four point as an elliptic point. -/
def pointFour (W : K) [(F W).IsElliptic] : (F W).toAffine.Point :=
  .mk (F_four_point_equation W)

def pointTwo (W : K) [(F W).IsElliptic] : (F W).toAffine.Point :=
  .mk ((F_equation_iff W 0 0).2 (by ring))

omit [CharZero K] in
theorem pointTwo_ne_zero (W : K) [(F W).IsElliptic] : pointTwo W ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

section Decidable
variable [DecidableEq K]

omit [CharZero K] in
theorem pointTwo_double (W : K) [(F W).IsElliptic] : pointTwo W+pointTwo W=0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [F, twistedF, WeierstrassCurve.Affine.negY]

theorem pointFour_double (W : K) [(F W).IsElliptic] :
    pointFour W+pointFour W=pointTwo W := by
  have hV := V_ne_zero_of_elliptic W
  have hW := W_add_lambda_ne_zero_of_elliptic W
  have hy : 2*V W*(W+lambda) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hV) hW
  have hneg : 2*V W*(W+lambda) ≠
      (F W).toAffine.negY (-V W) (2*V W*(W+lambda)) := by
    simp only [WeierstrassCurve.Affine.negY, F, twistedF, zero_mul, sub_zero]
    intro h
    apply hy
    linear_combination (1/2:K)*h
  change WeierstrassCurve.Affine.Point.some _ _ _ +
    WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some _ _ _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
  have hslope : (F W).toAffine.slope (-V W) (-V W)
      (2*V W*(W+lambda)) (2*V W*(W+lambda)) = -2*(W+lambda) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp only [F, twistedF, WeierstrassCurve.Affine.negY, zero_mul, sub_zero,
      one_mul, one_pow]
    field_simp
    unfold U V
    ring
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor <;>
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY] <;>
    rw [hslope] <;>
    simp only [WeierstrassCurve.Affine.negY, F, twistedF] <;>
    unfold U V <;> ring

theorem pointFour_quadruple (W : K) [(F W).IsElliptic] : (4:ℕ) • pointFour W=0 := by
  calc
    4 • pointFour W=(pointFour W+pointFour W)+(pointFour W+pointFour W) := by abel
    _=0 := by rw [pointFour_double, pointTwo_double]

theorem pointFour_order (W : K) [(F W).IsElliptic] : addOrderOf (pointFour W)=4 := by
  have htwo : (2:ℕ) • pointFour W ≠ 0 := by
    simpa only [two_nsmul, pointFour_double] using pointTwo_ne_zero W
  simpa using (addOrderOf_eq_prime_pow (p:=2) (n:=1) htwo (pointFour_quadruple W))

end Decidable

end Z2Z4Rank6.SecondFamily
