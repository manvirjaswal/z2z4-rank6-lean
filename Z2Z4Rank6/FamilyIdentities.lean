module

public import Z2Z4Rank6.Twists

@[expose] public section

/-!
# The Dujella–Peral parameter and the surface involution

Rational identities from Lemma 2.1 and Lemmas 3.1(c), 3.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. Denominator hypotheses state precisely
where these identities can be evaluated in a field.
-/

namespace Z2Z4Rank6

variable {K : Type*} [Field K] [CharZero K]

/-- The change of base parameter printed in Lemma 2.1. -/
def parameterM (t : K) : K := (t+1)/(t-1)

def parameterAlpha (t : K) : K := (49*t^2-100*t+49)/(7*(t^2-1))

def dpPlus (α τ : K) : K := (τ+α)*(1+α*τ)
def dpMinus (α τ : K) : K := (τ-α)*(1-α*τ)

def dpAPrime (t : K) : K := t*(5*t-4)*(5*t-6)*(49*t-50)
def dpBPrime (t : K) : K := (4*t-5)*(6*t-5)*(50*t-49)
def parameterRho (t : K) : K := (98*(t+1)/(t-1))^2

omit [CharZero K] in
private theorem t_sq_sub_one_ne_zero (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) : t^2-1 ≠ 0 := by
  have hp : t+1 ≠ 0 := by intro h; apply hn; linear_combination h
  rw [show t^2-1=(t-1)*(t+1) by ring]
  exact mul_ne_zero (sub_ne_zero.mpr h1) hp

omit [CharZero K] in
/-- The displayed expression for a after m=(t+1)/(t−1). -/
theorem a_parameterM (t : K) (h : t ≠ 1) :
    a (parameterM t)=112*dpAPrime t/(t-1)^4 := by
  unfold a parameterM dpAPrime
  field_simp
  ring

omit [CharZero K] in
/-- The displayed expression for b after m=(t+1)/(t−1). -/
theorem b_parameterM (t : K) (h : t ≠ 1) :
    b (parameterM t)=112*dpBPrime t/(t-1)^4 := by
  unfold b parameterM dpBPrime
  field_simp
  ring

/-- The Dujella–Peral A₊B₊ coefficient in Lemma 2.1. -/
theorem dpPlus_parameterAlpha (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) :
    dpPlus (parameterAlpha t) (1/7)=4*dpAPrime t/(343*(t^2-1)^2) := by
  have h2 := t_sq_sub_one_ne_zero t h1 hn
  unfold dpPlus parameterAlpha dpAPrime
  field_simp
  ring

/-- The Dujella–Peral A₋B₋ coefficient in Lemma 2.1. -/
theorem dpMinus_parameterAlpha (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) :
    dpMinus (parameterAlpha t) (1/7)= -4*dpBPrime t/(343*(t^2-1)^2) := by
  have h2 := t_sq_sub_one_ne_zero t h1 hn
  unfold dpMinus parameterAlpha dpBPrime
  field_simp
  ring

/-- The first coefficient is scaled by the printed square ρ. -/
theorem a_parameter_scale (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) :
    a (parameterM t)=parameterRho t*dpPlus (parameterAlpha t) (1/7) := by
  have h2 := t_sq_sub_one_ne_zero t h1 hn
  rw [a_parameterM t h1, dpPlus_parameterAlpha t h1 hn]
  unfold parameterRho
  field_simp
  ring

/-- The second coefficient is scaled by −ρ; its square has the same scale. -/
theorem b_parameter_scale (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) :
    b (parameterM t)= -parameterRho t*dpMinus (parameterAlpha t) (1/7) := by
  have h2 := t_sq_sub_one_ne_zero t h1 hn
  rw [b_parameterM t h1, dpMinus_parameterAlpha t h1 hn]
  unfold parameterRho
  field_simp
  ring

/-- The printed scaling factor is nonzero at every regular parameter. -/
theorem parameterRho_ne_zero (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) : parameterRho t ≠ 0 := by
  have hp : t+1 ≠ 0 := by intro h; apply hn; linear_combination h
  exact pow_ne_zero 2 (div_ne_zero (mul_ne_zero (by norm_num) hp) (sub_ne_zero.mpr h1))

/-- The admissible Weierstrass change corresponding to `(x,y)↦(r²x,r³y)`. -/
def scalingChange (r : Kˣ) : WeierstrassCurve.VariableChange K := ⟨r⁻¹,0,0,0⟩

omit [CharZero K] in
theorem scalingChange_E (r : Kˣ) (α β : K) :
    scalingChange r • E α β=E ((r : K)*α) ((r : K)*β) := by
  ext <;>
    simp [scalingChange, E, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆] <;> ring

/-- An admissible Weierstrass isomorphism takes the Dujella–Peral
equation at `(α_t,1/7)` to X, using exactly the scaling printed in Lemma 2.1. -/
theorem dp_parameter_isomorphism (t : K) (h1 : t ≠ 1) (hn : t ≠ -1) :
    scalingChange (Units.mk0 (parameterRho t) (parameterRho_ne_zero t h1 hn)) •
        E (dpPlus (parameterAlpha t) (1/7)) (dpMinus (parameterAlpha t) (1/7)) =
      X (parameterM t) := by
  rw [scalingChange_E]
  change E (parameterRho t*dpPlus (parameterAlpha t) (1/7))
      (parameterRho t*dpMinus (parameterAlpha t) (1/7)) = E (a (parameterM t)) (b (parameterM t))
  rw [a_parameter_scale t h1 hn, b_parameter_scale t h1 hn]
  ext <;> simp [E]

/-- The S coefficient is preserved by n↦9801/n with the printed fourth-power scale. -/
theorem surfaceS_involution (n : K) (hn : n ≠ 0) :
    surfaceS (9801/n)=(99/n)^4*surfaceS n := by
  unfold surfaceS
  field_simp
  ring

/-- The w coefficient is preserved by the same involution and scale. -/
theorem surfaceW_involution (n : K) (hn : n ≠ 0) :
    surfaceW (9801/n)=(99/n)^4*surfaceW n := by
  unfold surfaceW
  field_simp
  ring

/-- The involution exchanges the q₂ and nq₁ square classes. -/
theorem q2_involution (n : K) (hn : n ≠ 0) :
    q2 (9801/n)=(9/n)^2*(n*q1 n) := by
  unfold q2 q1
  field_simp
  ring

/-- The abscissae of the fourth and fifth twist points have the printed involution relation. -/
theorem t4x_involution (n : K) (hn : n ≠ 0) :
    t4x (9801/n)=(9/n)^2*(99/n)^4*t5x n := by
  unfold t4x t5x
  field_simp
  ring

/-- The ordinate relation fixes the sign left unspecified in Lemma 3.2. -/
theorem t4y_involution (n : K) (hn : n ≠ 0) :
    t4y (9801/n)= -(9/n)^3*(99/n)^6*t5y n := by
  unfold t4y t5y twistN
  field_simp
  ring

section Ring

variable {R : Type*} [CommRing R]

/-- The displayed factorization of `S²−4w²` in Lemma 3.1. -/
theorem surfaceS_sq_sub_fourW_sq (n : R) :
    (surfaceS n)^2-4*(surfaceW n)^2=
      196*1960000*n*(n-99)^2*(twistN n)^2 := by
  calc
    _=(surfaceS n-2*surfaceW n)*(surfaceS n+2*surfaceW n) := by ring
    _=_ := by rw [surfaceS_sub_twoW, surfaceS_add_twoW]; ring

/-- The discriminant product in Lemma 3.1(b), with its nonzero constant explicit. -/
theorem surface_discriminant_factorization (n : R) :
    16*(surfaceW n)^4*((surfaceS n)^2-4*(surfaceW n)^2)=
      (16*49^4*196*1960000)*(n-1)^4*(n-81)^4*(n-121)^4*(n-9801)^4*
        n*(n-99)^2*(twistN n)^2 := by
  rw [surfaceS_sq_sub_fourW_sq]
  unfold surfaceW
  ring

end Ring

end Z2Z4Rank6
