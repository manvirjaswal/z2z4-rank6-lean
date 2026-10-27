module

public import Z2Z4Rank6.FamilyIdentities
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# The second family over G₂

Parameters, equations and identities in Section 8 of M. Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117, equations preceding Theorem 8.1.

All identities hold over any field of characteristic zero. The affine G₂ point type below means the
three printed equations.
-/

namespace Z2Z4Rank6.SecondFamily

variable {K : Type*} [Field K]

def mu : K := 19/33
def lambda : K := 361/1089
def beta : K := (161/1089)^2
def gamma : K := (361/161)^2

def U (W : K) : K := 2*(1+lambda)^2*W+2*(W+lambda)^2
def V (W : K) : K := -(W-1)*(W-lambda^2)

/-- The printed quadratic twist F^q, including q=1 for F itself. -/
def twistedF (W q : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := q*U W
  a₃ := 0
  a₄ := q^2*(V W)^2
  a₆ := 0

def F (W : K) : WeierstrassCurve K := twistedF W 1

def qA (W : K) : K := 29*(W-beta)
def qB (W : K) : K := -29*beta*(W-gamma)
def qH (W : K) : K := -(W-beta)*(W-gamma)

/-- An affine point of G₂, expressed by the exact three printed square equations. -/
@[ext]
structure G2Point (K : Type*) [Field K] where
  W : K
  s1 : K
  s2 : K
  s3 : K
  s1_sq : s1^2=W
  s2_sq : s2^2=qA W
  s3_sq : s3^2=qB W

theorem twistedF_equation_iff (W q x y : K) :
    (twistedF W q).toAffine.Equation x y ↔
      y^2=x*(x^2+q*U W*x+q^2*(V W)^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twistedF, zero_mul, add_zero]
  have h : x^3+q*U W*x^2+q^2*V W^2*x =
      x*(x^2+q*U W*x+q^2*(V W)^2) := by ring
  rw [h]

theorem F_equation_iff (W x y : K) :
    (F W).toAffine.Equation x y ↔ y^2=x*(x^2+U W*x+(V W)^2) := by
  simpa only [F, one_mul, one_pow] using twistedF_equation_iff W 1 x y

theorem U_sub_twoV (W : K) : U W-2*V W=4*(W+lambda)^2 := by
  unfold U V
  ring

theorem U_add_twoV (W : K) : U W+2*V W=4*(1+lambda)^2*W := by
  unfold U V
  ring

theorem U_sq_sub_fourV_sq (W : K) :
    (U W)^2-4*(V W)^2=16*(1+lambda)^2*W*(W+lambda)^2 := by
  have h : (U W)^2-4*(V W)^2=(U W-2*V W)*(U W+2*V W) := by ring
  rw [h, U_sub_twoV, U_add_twoV]
  ring

theorem F_discriminant (W : K) :
    (F W).Δ=16*(V W)^4*((U W)^2-4*(V W)^2) := by
  simp only [F, twistedF, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem twistedF_discriminant (W q : K) :
    (twistedF W q).Δ=q^6*(F W).Δ := by
  rw [F_discriminant]
  simp only [twistedF, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem F_split (s : K) :
    F (s^2)=E ((s-1)*(s-lambda)) ((s+1)*(s+lambda)) := by
  ext <;> simp only [F, twistedF, E, U, V] <;> ring

theorem F_four_point_equation (W : K) :
    (F W).toAffine.Equation (-V W) (2*V W*(W+lambda)) := by
  rw [F_equation_iff]
  have h := U_sub_twoV W
  calc
    _=(V W)^2*(U W-2*V W) := by rw [h]; ring
    _=_ := by ring

variable [CharZero K]

theorem lambda_eq_mu_sq : (lambda : K)=mu^2 := by norm_num [lambda, mu]
theorem gamma_eq : (gamma : K)=lambda^2/beta := by norm_num [gamma, lambda, beta]
theorem lambda_ne_zero : (lambda : K) ≠ 0 := by norm_num [lambda]
theorem beta_ne_zero : (beta : K) ≠ 0 := by norm_num [beta]

/-- The chosen parameters satisfy both section-prescription equations printed
before the definition of G₂. This does not claim uniqueness of their intersection. -/
theorem first_parameter_equation :
    (lambda : K)^4-16*lambda^3+(16*beta+30)*lambda^2+
      (160*beta-16)*lambda+64*beta^2+16*beta+1=0 := by
  norm_num [lambda, beta]

theorem second_parameter_equation :
    16*(lambda : K)^4+32*lambda^3+(8-8*beta)*lambda^2-
      (24*beta+8)*lambda+beta^2-18*beta+1=0 := by
  norm_num [lambda, beta]

theorem dpPlus_identification (s : K) :
    dpPlus (33/19) ((33/19)*s)=(33/19)^3*(s+1)*(s+lambda) := by
  norm_num [dpPlus, lambda]
  ring

theorem dpMinus_identification (s : K) :
    dpMinus (33/19) ((33/19)*s)=-(33/19)^3*(s-1)*(s-lambda) := by
  norm_num [dpMinus, lambda]
  ring

/-- The exact square-class relation printed for the three twists. -/
theorem qA_mul_qB (W : K) : qA W*qB W=(4669/1089)^2*qH W := by
  norm_num [qA, qB, qH, beta]
  ring

theorem qA_mul_qB_div_qH (W : K) (hH : qH W ≠ 0) :
    qA W*qB W/qH W=(4669/1089)^2 := by
  rw [qA_mul_qB, mul_div_cancel_right₀ _ hH]

/-- The involution of the W-line used to obtain Q₄ and Q₅. -/
def sigma (W : K) : K := lambda^2/W

theorem sigma_involutive (W : K) (hW : W ≠ 0) : sigma (sigma W)=W := by
  unfold sigma
  field_simp [hW, lambda_ne_zero]

theorem U_involution (W : K) (hW : W ≠ 0) :
    U (sigma W)=(lambda/W)^2*U W := by
  unfold U sigma
  field_simp
  ring

omit [CharZero K] in
theorem V_involution (W : K) (hW : W ≠ 0) :
    V (sigma W)=(lambda/W)^2*V W := by
  unfold V sigma
  field_simp
  ring

theorem qA_involution (W : K) (hW : W ≠ 0) : qA (sigma W)=qB W/W := by
  unfold qA qB sigma
  norm_num [lambda, beta, gamma]
  field_simp
  ring

/-- The coordinate scale in the paper's involution. -/
def iotaScale (W : K) : K := W^2/lambda

/-- Transport of the displayed equation through the involution, before untwisting.
This is a coordinate assertion and does not assert a function-field group isomorphism. -/
theorem iota_equation (W x y : K) (hW : W ≠ 0)
    (h : y^2=x*(x^2+qA (sigma W)*U (sigma W)*x+
      (qA (sigma W))^2*(V (sigma W))^2)) :
    (iotaScale W^3*y)^2=(iotaScale W^2*x)*
      ((iotaScale W^2*x)^2+(W*qB W)*U W*(iotaScale W^2*x)+
        (W*qB W)^2*(V W)^2) := by
  rw [mul_pow, h, U_involution W hW, V_involution W hW, qA_involution W hW]
  unfold iotaScale
  field_simp [hW, lambda_ne_zero]

/-- The square root of q_H on the printed affine base G₂. -/
theorem G2Point.qH_square (P : G2Point K) :
    (1089*P.s2*P.s3/4669)^2=qH P.W := by
  have h := qA_mul_qB P.W
  rw [← P.s2_sq, ← P.s3_sq] at h
  calc
    (1089*P.s2*P.s3/4669)^2 =
        (1089/4669)^2*(P.s2^2*P.s3^2) := by ring
    _ = (1089/4669)^2*((4669/1089)^2*qH P.W) := by rw [h]
    _ = qH P.W := by norm_num; ring

theorem qH_ne_zero_of_qA_qB (W : K) (hA : qA W ≠ 0) (hB : qB W ≠ 0) :
    qH W ≠ 0 := by
  have h := mul_ne_zero hA hB
  rw [qA_mul_qB] at h
  exact (mul_ne_zero_iff.1 h).2

/-- The conic parametrization used in Theorem 8.1(a). -/
def thetaS1 (theta : K) : K := (161/1089)*(theta^2+29)/(theta^2-29)
def thetaS2 (theta : K) : K := theta*(thetaS1 theta-161/1089)
def thetaEta (theta s3 : K) : K := (1185921/58)*s3*(theta^2-29)
def thetaQuartic (theta : K) : K :=
  1326538900*theta^4-77611154441*theta^2+1115619214900

theorem theta_conic (theta : K) (h : theta^2-29 ≠ 0) :
    (thetaS2 theta)^2=qA ((thetaS1 theta)^2) := by
  norm_num [thetaS1, thetaS2, qA, beta]
  field_simp
  ring

/-- Exact identity behind the printed quartic, with the coordinate denominator
cleared. Its nonzero prefactor gives the equivalence of the two equations. -/
theorem theta_quartic_identity (theta s3 : K) (h : theta^2-29 ≠ 0) :
    thetaEta theta s3^2-thetaQuartic theta =
      (1185921/58)^2*(theta^2-29)^2*(s3^2-qB ((thetaS1 theta)^2)) := by
  norm_num [thetaEta, thetaQuartic, thetaS1, qB, beta, gamma]
  field_simp
  ring

theorem theta_third_iff_quartic (theta s3 : K) (h : theta^2-29 ≠ 0) :
    s3^2=qB ((thetaS1 theta)^2) ↔ thetaEta theta s3^2=thetaQuartic theta := by
  have hc : (1185921/58 : K)^2*(theta^2-29)^2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 h)
  constructor
  · intro h3
    apply sub_eq_zero.mp
    rw [theta_quartic_identity theta s3 h, h3, sub_self, mul_zero]
  · intro h3
    have hz : (1185921/58)^2*(theta^2-29)^2*
        (s3^2-qB ((thetaS1 theta)^2))=0 := by
      rw [← theta_quartic_identity theta s3 h, h3, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hc)

/-- Affine G₂ point obtained from a point on the printed quartic chart. -/
def thetaG2Point (theta s3 : K) (h : theta^2-29 ≠ 0)
    (h3 : thetaEta theta s3^2=thetaQuartic theta) : G2Point K where
  W := (thetaS1 theta)^2
  s1 := thetaS1 theta
  s2 := thetaS2 theta
  s3 := s3
  s1_sq := rfl
  s2_sq := theta_conic theta h
  s3_sq := (theta_third_iff_quartic theta s3 h).2 h3

/-- Over Q the square equations exclude W=0 and W=-λ. -/
theorem G2Point.rational_W_pos (P : G2Point ℚ) : 0 < P.W := by
  have h := sq_nonneg P.s2
  rw [P.s2_sq] at h
  norm_num [qA, beta] at h
  linarith

theorem G2Point.rational_elliptic_iff (P : G2Point ℚ) :
    (F P.W).IsElliptic ↔ P.W ≠ 1 ∧ P.W ≠ (lambda : ℚ)^2 := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    F_discriminant, U_sq_sub_fourV_sq]
  have hW := P.rational_W_pos
  have hplus : P.W+(lambda : ℚ) ≠ 0 := by norm_num [lambda]; linarith
  have hl : 1+(lambda : ℚ) ≠ 0 := by norm_num [lambda]
  have hW0 : P.W ≠ 0 := ne_of_gt hW
  simp only [V, mul_ne_zero_iff, pow_ne_zero_iff (by decide : 4 ≠ 0),
    pow_ne_zero_iff (by decide : 2 ≠ 0), neg_ne_zero, sub_ne_zero]
  norm_num only at *
  tauto


def signedRoot (b : Bool) (r : ℚ) : ℚ := if b then r else -r

theorem signedRoot_sq (b : Bool) (r : ℚ) : signedRoot b r^2=r^2 := by
  cases b <;> simp [signedRoot]

theorem signedRoot_injective {r : ℚ} (hr : r ≠ 0) :
    Function.Injective (fun b => signedRoot b r) := by
  intro a b h
  cases a <;> cases b
  · rfl
  · exfalso; apply hr; dsimp [signedRoot] at h; linarith
  · exfalso; apply hr; dsimp [signedRoot] at h; linarith
  · rfl

theorem exists_signedRoot {x r : ℚ} (h : x^2=r^2) : ∃ b, signedRoot b r=x := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).1 h with h | h
  · exact ⟨true, by simpa [signedRoot] using h.symm⟩
  · exact ⟨false, by simpa [signedRoot] using h.symm⟩

def singularS1 (b : Bool) : ℚ := if b then 1 else lambda
def singularS2 (b : Bool) : ℚ := if b then 5800/1089 else 580/363
def singularS3 (b : Bool) : ℚ := if b then 580/363 else 2093800/1185921

/-- The two singular W fibers, with the independent three square-root signs. -/
def singularPoint (t : Bool × (Fin 3 → Bool)) : G2Point ℚ where
  W := (singularS1 t.1)^2
  s1 := signedRoot (t.2 0) (singularS1 t.1)
  s2 := signedRoot (t.2 1) (singularS2 t.1)
  s3 := signedRoot (t.2 2) (singularS3 t.1)
  s1_sq := signedRoot_sq _ _
  s2_sq := by rw [signedRoot_sq]; cases t.1 <;> norm_num [singularS1, singularS2, qA, beta, lambda]
  s3_sq := by rw [signedRoot_sq]; cases t.1 <;> norm_num [singularS1, singularS3, qB, beta, gamma, lambda]

theorem singularPoint_injective : Function.Injective singularPoint := by
  rintro ⟨a, e⟩ ⟨b, f⟩ h
  have hW := congrArg G2Point.W h
  have hab : a=b := by
    cases a <;> cases b <;> first | rfl | norm_num [singularPoint, singularS1, lambda] at hW
  subst b
  apply congrArg (fun z => (a,z))
  funext i
  fin_cases i
  · apply signedRoot_injective (r:=singularS1 a) (by cases a <;> norm_num [singularS1, lambda])
    exact congrArg G2Point.s1 h
  · apply signedRoot_injective (r:=singularS2 a) (by cases a <;> norm_num [singularS2])
    exact congrArg G2Point.s2 h
  · apply signedRoot_injective (r:=singularS3 a) (by cases a <;> norm_num [singularS3])
    exact congrArg G2Point.s3 h

theorem mem_singularPoint_range_iff (P : G2Point ℚ) :
    P ∈ Set.range singularPoint ↔ P.W=1 ∨ P.W=(lambda:ℚ)^2 := by
  constructor
  · rintro ⟨⟨b,e⟩,rfl⟩
    cases b <;> simp [singularPoint, singularS1]
  · intro hW
    have go (b : Bool) (hb : P.W=(singularS1 b)^2) : P ∈ Set.range singularPoint := by
      have h1 : P.s1^2=(singularS1 b)^2 := P.s1_sq.trans hb
      have h2 : P.s2^2=(singularS2 b)^2 := by
        rw [P.s2_sq, hb]
        cases b <;> norm_num [qA, beta, singularS1, singularS2, lambda]
      have h3 : P.s3^2=(singularS3 b)^2 := by
        rw [P.s3_sq, hb]
        cases b <;> norm_num [qB, beta, gamma, singularS1, singularS3, lambda]
      obtain ⟨e1,he1⟩ := exists_signedRoot h1
      obtain ⟨e2,he2⟩ := exists_signedRoot h2
      obtain ⟨e3,he3⟩ := exists_signedRoot h3
      refine ⟨⟨b,![e1,e2,e3]⟩, ?_⟩
      apply G2Point.ext
      · exact hb.symm
      · exact he1
      · exact he2
      · exact he3
    rcases hW with hW | hW
    · exact go true (by simpa [singularS1] using hW)
    · exact go false (by simpa [singularS1] using hW)

theorem singular_fiber_points_ncard :
    {P : G2Point ℚ | ¬(F P.W).IsElliptic}.ncard=16 := by
  have hs : {P : G2Point ℚ | ¬(F P.W).IsElliptic}=Set.range singularPoint := by
    ext P
    rw [Set.mem_ofPred_eq, P.rational_elliptic_iff, mem_singularPoint_range_iff]
    tauto
  rw [hs, Set.ncard_range_of_injective singularPoint_injective]
  norm_num [Nat.card_eq_fintype_card]


def singularThetaProduct (t : ℚ) : ℚ :=
  (t-10/3)*(t+10/3)*(t-87/10)*(t+87/10)*
    (t-25/4)*(t+25/4)*(t-116/25)*(t+116/25)

theorem theta_singular_factorization (t : ℚ) (h : t^2-29 ≠ 0) :
    (t^2-29)^4*((thetaS1 t)^2-1)*((thetaS1 t)^2-lambda^2)=
      (beta-1)*(beta-lambda^2)*singularThetaProduct t := by
  norm_num [thetaS1, beta, lambda, singularThetaProduct]
  field_simp
  ring

theorem theta_singular_iff (t : ℚ) (h : t^2-29 ≠ 0) :
    (thetaS1 t)^2=1 ∨ (thetaS1 t)^2=(lambda:ℚ)^2 ↔
      t ∈ ({10/3,-10/3,87/10,-87/10,25/4,-25/4,116/25,-116/25} : Set ℚ) := by
  have hc : ((beta:ℚ)-1)*(beta-lambda^2) ≠ 0 := by norm_num [beta, lambda]
  have hd : (t^2-29)^4 ≠ 0 := pow_ne_zero 4 h
  have hi := theta_singular_factorization t h
  have hp : ((thetaS1 t)^2=1 ∨ (thetaS1 t)^2=(lambda:ℚ)^2) ↔
      singularThetaProduct t=0 := by
    constructor
    · rintro (hW|hW)
      · have hz : ((beta:ℚ)-1)*(beta-lambda^2)*singularThetaProduct t=0 := by
          rw [← hi, hW]; ring
        exact (mul_eq_zero.mp hz).resolve_left hc
      · have hz : ((beta:ℚ)-1)*(beta-lambda^2)*singularThetaProduct t=0 := by
          rw [← hi, hW]; ring
        exact (mul_eq_zero.mp hz).resolve_left hc
    · intro hz
      have hz' : (t^2-29)^4*(((thetaS1 t)^2-1)*((thetaS1 t)^2-lambda^2))=0 := by
        rw [← mul_assoc, hi, hz, mul_zero]
      have hz'' := (mul_eq_zero.mp hz').resolve_left hd
      simpa only [mul_eq_zero, sub_eq_zero] using hz''
  simpa only [singularThetaProduct, mul_eq_zero, sub_eq_zero,
    add_eq_zero_iff_eq_neg, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_div, or_assoc] using hp

end Z2Z4Rank6.SecondFamily
