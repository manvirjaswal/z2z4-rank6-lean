import Z2Z4Rank6.SecondParameterSelection
import Z2Z4Rank6.SecondSections
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The two prescribed generic sections and their exceptional parameters

Explicit sections on twists by constant multiples of W-beta are obtained from
the two printed parameter equations. The constant multiples are computed;
their vanishing gives exactly the two printed exceptional points. At the
chosen parameters both constants are 29 times explicit rational squares.
-/
namespace Z2Z4Rank6.SecondParameterSelection
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- The coefficients of the second family before fixing lambda. -/
def genericU (l t : K) : K := 2*(1+l)^2*t+2*(t+l)^2
def genericV (l t : K) : K := -(t-1)*(t-l^2)

def twistedModel (l t q : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := q*genericU l t
  a₃ := 0
  a₄ := q^2*(genericV l t)^2
  a₆ := 0

omit [CharZero K] in
/-- Fixing lambda gives exactly the printed second-family twist model. -/
theorem chosen_model (t q : K) :
    twistedModel (SecondFamily.lambda : K) t q=SecondFamily.twistedF t q := rfl

omit [CharZero K] in
theorem twistedModel_equation (l t q x y : K) :
    (twistedModel l t q).toAffine.Equation x y ↔
      y^2=x*(x^2+q*genericU l t*x+q^2*(genericV l t)^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twistedModel,WeierstrassCurve.toAffine]
  ring_nf

/-- The first constant multiple of W-beta. -/
def firstMultiplier (l b : K) : K := ((l-1)^2-4*b)/12

/-- The second constant multiple; lambda=-1 is excluded. -/
def secondNumerator (l b : K) : K := 8*l^3+4*l^2-4*l+1-(4*l+5)*b
def secondMultiplier (l b : K) : K := secondNumerator l b/(8*(l+1))

def firstSquare (l b t : K) : K :=
  t^2+(firstMultiplier l b-b-(l^2+1)/2)*t-l*(b-firstMultiplier l b)

def secondRoot (l b : K) : K := (2*l^2+1-2*secondMultiplier l b-b)/2

def firstQuartic (l b k t : K) : K :=
  (t-b)^2*(t-1)*(t-l^2)+k*(t-b)*genericU l t+k^2*(t-1)*(t-l^2)

def secondCubic (l k t : K) : K :=
  k^2*(t-1)+k*genericU l t+(t-1)*(t-l^2)^2

/-- The exact square-prescription remainder for the first section. -/
theorem first_square_identity (l b t : K) :
    firstQuartic l b (firstMultiplier l b) t-(firstSquare l b t)^2=
      -t*(l+1)^2*firstCondition l b/144 := by
  unfold firstQuartic firstSquare firstMultiplier genericU firstCondition
  field_simp
  ring

/-- The exact square-prescription remainder for the second section. -/
theorem second_square_identity (l b t : K) (hl : l≠-1) :
    secondCubic l (secondMultiplier l b) t-(t-b)*(t-secondRoot l b)^2=
      (16*t*l^2+24*t*l+8*t+b-1)*secondCondition l b/(64*(l+1)^2) := by
  have hp : l+1≠0 := by intro h; apply hl; linear_combination h
  unfold secondCubic secondRoot secondMultiplier secondNumerator genericU secondCondition
  field_simp
  ring

def firstX (l b t : K) : K := (firstMultiplier l b)^2*(t-1)*(t-l^2)
def firstY (l b t : K) : K :=
  (firstMultiplier l b)^2*(t-1)*(t-l^2)*firstSquare l b t

def secondX (l b t : K) : K := (secondMultiplier l b)^2*(t-1)*(t-b)
def secondY (l b t : K) : K :=
  (secondMultiplier l b)^2*(t-1)*(t-b)^2*(t-secondRoot l b)

/-- A point equation of the prescribed first shape. -/
theorem first_section_equation (l b t : K) (h : firstCondition l b=0) :
    (twistedModel l t (firstMultiplier l b*(t-b))).toAffine.Equation
      (firstX l b t) (firstY l b t) := by
  rw [twistedModel_equation]
  have hs : firstQuartic l b (firstMultiplier l b) t=(firstSquare l b t)^2 := by
    have hh := first_square_identity l b t
    rw [h,mul_zero,zero_div] at hh
    exact sub_eq_zero.mp hh
  calc
    _=(firstMultiplier l b)^4*((t-1)*(t-l^2))^2*(firstSquare l b t)^2 := by
      unfold firstY
      ring
    _=(firstMultiplier l b)^4*((t-1)*(t-l^2))^2*
        firstQuartic l b (firstMultiplier l b) t := by rw [hs]
    _=_ := by unfold firstX firstQuartic genericV; ring

/-- A point equation of the prescribed second shape. -/
theorem second_section_equation (l b t : K) (hl : l≠-1) (h : secondCondition l b=0) :
    (twistedModel l t (secondMultiplier l b*(t-b))).toAffine.Equation
      (secondX l b t) (secondY l b t) := by
  rw [twistedModel_equation]
  have hs : secondCubic l (secondMultiplier l b) t=(t-b)*(t-secondRoot l b)^2 := by
    have hh := second_square_identity l b t hl
    rw [h,mul_zero,zero_div] at hh
    exact sub_eq_zero.mp hh
  calc
    _=(secondMultiplier l b)^4*(t-1)^2*(t-b)^3*((t-b)*(t-secondRoot l b)^2) := by
      unfold secondY
      ring
    _=(secondMultiplier l b)^4*(t-1)^2*(t-b)^3*
        secondCubic l (secondMultiplier l b) t := by rw [hs]
    _=_ := by unfold secondX secondCubic genericV; ring

omit [CharZero K] in
theorem generic_discriminant (l t q : K) :
    (twistedModel l t q).Δ=
      256*q^6*(t-1)^4*(t-l^2)^4*(l+1)^2*t*(t+l)^2 := by
  simp only [twistedModel,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  unfold genericU genericV
  ring

omit [CharZero K] in
/-- The printed lambda=-1 degeneration has zero discriminant. -/
theorem minus_one_singular (t q : K) : (twistedModel (-1) t q).Δ=0 := by
  rw [generic_discriminant]
  ring

omit [CharZero K] in
/-- The lambda=-1 model fails the ellipticity predicate. -/
theorem minus_one_not_elliptic (t q : K) : ¬(twistedModel (-1) t q).IsElliptic := by
  rintro ⟨hd⟩
  rw [minus_one_singular] at hd
  exact not_isUnit_zero hd

/-- First exceptional parameter pair, with no other zero twist coefficient. -/
theorem first_multiplier_zero (l b : ℚ) (hl : l≠-1) (h : firstCondition l b=0) :
    firstMultiplier l b=0 ↔ l=1 ∧ b=0 := by
  constructor
  · intro hk
    have hb : b=(l-1)^2/4 := by
      unfold firstMultiplier at hk
      linarith
    have hf : 9*(l-1)^2*(l+1)^2=0 := by
      calc
        _=firstCondition l ((l-1)^2/4) := by unfold firstCondition; ring
        _=0 := by rw [←hb]; exact h
    have hp : (l+1)^2≠0 := pow_ne_zero 2 (by intro hh; apply hl; linarith)
    have hz : (l-1)^2=0 := by
      rcases mul_eq_zero.mp hf with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      · exact False.elim (hp hh)
    have he : l=1 := by have hh := sq_eq_zero_iff.mp hz; linarith
    subst l
    norm_num at hb
    exact ⟨rfl,hb⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [firstMultiplier]

omit [CharZero K] in
/-- Bezout certificate for the zero second twist coefficient. -/
theorem second_zero_elimination (l b : K) :
    (4*l+5)^2*secondCondition l b-
      (-(4*l+5)*b-(4*l+5)*secondLinearCoefficient l-
        (8*l^3+4*l^2-4*l+1))*secondNumerator l b=
      64*(l-1)^3*(l+1)^3 := by
  unfold secondCondition secondLinearCoefficient secondNumerator
  ring

/-- Second exceptional parameter pair, with no other zero twist coefficient. -/
theorem second_multiplier_zero (l b : ℚ) (hl : l≠-1) (h : secondCondition l b=0) :
    secondMultiplier l b=0 ↔ l=1 ∧ b=1 := by
  constructor
  · intro hk
    have hn : secondNumerator l b=0 := (div_eq_zero_iff.mp hk).resolve_right (by
      apply mul_ne_zero (by norm_num)
      intro hh
      apply hl
      linarith)
    have hf : 64*(l-1)^3*(l+1)^3=0 := by
      rw [←second_zero_elimination,h,hn]
      ring
    have hp : (l+1)^3≠0 := pow_ne_zero 3 (by intro hh; apply hl; linarith)
    have hz : (l-1)^3=0 := by
      rcases mul_eq_zero.mp hf with hh | hh
      · exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
      · exact False.elim (hp hh)
    have he : l=1 := by have hh := eq_zero_of_pow_eq_zero hz; linarith
    subst l
    norm_num [secondNumerator] at hn
    exact ⟨rfl,by linarith⟩
  · rintro ⟨rfl,rfl⟩
    norm_num [secondMultiplier,secondNumerator]

/-- Both selected twist constants are 29 times nonzero rational squares. -/
theorem chosen_twist_constants :
    firstMultiplier (SecondFamily.lambda : ℚ) SecondFamily.beta=29*(35/1089)^2 ∧
    secondMultiplier (SecondFamily.lambda : ℚ) SecondFamily.beta=29*(32/1089)^2 := by
  norm_num [firstMultiplier,secondMultiplier,secondNumerator,SecondFamily.lambda,SecondFamily.beta]

end
end Z2Z4Rank6.SecondParameterSelection
