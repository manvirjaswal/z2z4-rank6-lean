import Z2Z4Rank6.Sections

/-!
# The three twist sections

Polynomial identities from Lemmas 3.1 and 3.2 and the square-root transport of
Proposition 4.2 of Manvir Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*, DOI 10.5281/zenodo.23437117.
The data are transcribed from the displayed formulas, with their printed signs.
-/

namespace Z2Z4Rank6

section Ring

variable {R : Type*} [CommRing R]

def surfaceS (n : R) : R :=
  98 * (n^4 + 9996*n^3 - 1960394*n^2 + 97970796*n + 96059601)

def surfaceW (n : R) : R := -49*(n-1)*(n-81)*(n-121)*(n-9801)

def q1 (n : R) : R := 5*(3*n+242)
def q2 (n : R) : R := 5*(2*n+243)
def q12 (n : R) : R := (3*n+242)*(2*n+243)
def twistN (n : R) : R := n^2-2*n+9801

def t4x (n : R) : R := 49*(n-1)*(n-81)*(n-121)^2*(2*n+243)^2
def t5x (n : R) : R := 49*(n-9801)*(n-121)*(n-81)^2*(3*n+242)^2
def t6x (n : R) : R := 49*(n-9801)*(n-1)*(n-121)^2*(2*n+243)^2

def t4y (n : R) : R :=
  -686*(n-1)*(n-36)*(n-81)*(n-121)^2*(2*n+243)^2*twistN n
def t5y (n : R) : R :=
  -686*(n-9801)*(n-121)*(4*n-1089)*(n-81)^2*(3*n+242)^2*twistN n
def t6y (n : R) : R :=
  -1715*(n-9801)*(n-1)*(n-99)*(n-121)^2*(2*n+243)^2*twistN n

theorem a_neg (m : R) : a (-m) = -b m := by unfold a b; ring
theorem b_neg (m : R) : b (-m) = -a m := by unfold a b; ring
theorem a_sub_b (m : R) : a m - b m = 14*(m^4-2*m^2+9801) := by unfold a b; ring
theorem a_add_b (m : R) : a m + b m = -1400*m*(m^2-99) := by unfold a b; ring

theorem surfaceS_base_change (m : R) : surfaceS (m^2) = (a m)^2+(b m)^2 := by
  unfold surfaceS a b
  ring

theorem surfaceW_base_change (m : R) : surfaceW (m^2) = a m*b m := by
  unfold surfaceW a b
  ring

theorem surfaceS_sub_twoW (n : R) : surfaceS n-2*surfaceW n = 196*(twistN n)^2 := by
  unfold surfaceS surfaceW twistN
  ring

theorem surfaceS_add_twoW (n : R) : surfaceS n+2*surfaceW n = 1960000*n*(n-99)^2 := by
  unfold surfaceS surfaceW
  ring

theorem q1_mul_q2 (n : R) : q1 n*q2 n = 25*q12 n := by
  unfold q1 q2 q12
  ring

/-- The first expanded factorization in the proof of Lemma 3.2. -/
theorem t4_factorization (n : R) :
    (t4x n)^2 + q2 n*surfaceS n*t4x n + (q2 n)^2*(surfaceW n)^2 =
      9604*(n-1)*(n-81)*(n-36)^2*(n-121)^2*(2*n+243)^2*(twistN n)^2 := by
  unfold t4x q2 surfaceS surfaceW twistN
  ring

/-- The second expanded factorization in the proof of Lemma 3.2. -/
theorem t5_factorization (n : R) :
    (t5x n)^2 + n*q1 n*surfaceS n*t5x n + (n*q1 n)^2*(surfaceW n)^2 =
      9604*(n-9801)*(n-121)*(n-81)^2*(3*n+242)^2*(4*n-1089)^2*(twistN n)^2 := by
  unfold t5x q1 surfaceS surfaceW twistN
  ring

/-- The third expanded factorization in the proof of Lemma 3.2. -/
theorem t6_factorization (n : R) :
    (t6x n)^2 + q12 n*surfaceS n*t6x n + (q12 n)^2*(surfaceW n)^2 =
      60025*(n-9801)*(n-1)*(n-99)^2*(n-121)^2*(2*n+243)^2*(twistN n)^2 := by
  unfold t6x q12 surfaceS surfaceW twistN
  ring

/-- The printed fourth point lies on the twist by q₂. -/
theorem t4_equation (n : R) :
    (t4y n)^2 = t4x n*((t4x n)^2+q2 n*surfaceS n*t4x n+(q2 n)^2*(surfaceW n)^2) := by
  rw [t4_factorization]
  unfold t4y t4x
  ring

/-- The printed fifth point lies on the twist by nq₁. -/
theorem t5_equation (n : R) :
    (t5y n)^2 = t5x n*((t5x n)^2+n*q1 n*surfaceS n*t5x n+(n*q1 n)^2*(surfaceW n)^2) := by
  rw [t5_factorization]
  unfold t5y t5x
  ring

/-- The printed sixth point lies on the twist by q₁₂. -/
theorem t6_equation (n : R) :
    (t6y n)^2 = t6x n*((t6x n)^2+q12 n*surfaceS n*t6x n+(q12 n)^2*(surfaceW n)^2) := by
  rw [t6_factorization]
  unfold t6y t6x
  ring

end Ring

section Field

variable {K : Type*} [Field K]

/-- The square-root map from a quadratic twist used before Lemma 3.1. -/
theorem untwist_equation (S w q r x y : K) (hq : q ≠ 0) (hr : r^2=q)
    (h : y^2=x*(x^2+q*S*x+q^2*w^2)) :
    (y/(q*r))^2 = (x/q)*((x/q)^2+S*(x/q)+w^2) := by
  rw [div_pow, mul_pow, hr, h]
  field_simp

def p4x (m : K) : K := t4x (m^2)/q2 (m^2)
def p4y (m v : K) : K := t4y (m^2)/(q2 (m^2)*v)
def p5x (m : K) : K := t5x (m^2)/(m^2*q1 (m^2))
def p5y (m u : K) : K := t5y (m^2)/(m^2*q1 (m^2)*m*u)
def p6x (m : K) : K := t6x (m^2)/q12 (m^2)
def p6y (m u v : K) : K := t6y (m^2)/(q12 (m^2)*(u*v/5))

private theorem cubic_of_surface_equation (m x y : K)
    (h : y^2=x*(x^2+surfaceS (m^2)*x+(surfaceW (m^2))^2)) :
    y^2=x*(x+(a m)^2)*(x+(b m)^2) := by
  rw [surfaceS_base_change, surfaceW_base_change] at h
  rw [h]
  ring

/-- The fourth section of Proposition 4.2, with its necessary nonzero square root. -/
theorem p4_equation (m v : K) (hv : v^2=q2 (m^2)) (hv0 : v ≠ 0) :
    (p4y m v)^2=p4x m*(p4x m+(a m)^2)*(p4x m+(b m)^2) := by
  apply cubic_of_surface_equation
  exact untwist_equation _ _ _ _ _ _ (hv ▸ pow_ne_zero 2 hv0) hv (t4_equation (m^2))

/-- The fifth section of Proposition 4.2. -/
theorem p5_equation (m u : K) (hu : u^2=q1 (m^2)) (hm : m ≠ 0) (hu0 : u ≠ 0) :
    (p5y m u)^2=p5x m*(p5x m+(a m)^2)*(p5x m+(b m)^2) := by
  apply cubic_of_surface_equation
  have hr : (m*u)^2=m^2*q1 (m^2) := by rw [mul_pow, hu]
  have hq : m^2*q1 (m^2) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hm) (hu ▸ pow_ne_zero 2 hu0)
  simpa only [p5x, p5y, mul_assoc] using
    untwist_equation (surfaceS (m^2)) (surfaceW (m^2)) (m^2*q1 (m^2)) (m*u)
      (t5x (m^2)) (t5y (m^2)) hq hr (t5_equation (m^2))

variable [CharZero K]

/-- The product square root used by the sixth section. -/
theorem product_root_sq (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2)) :
    (u*v/5)^2=q12 (m^2) := by
  rw [div_pow, mul_pow, hu, hv, q1_mul_q2]
  field_simp
  ring

/-- The sixth section of Proposition 4.2. -/
theorem p6_equation (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    (p6y m u v)^2=p6x m*(p6x m+(a m)^2)*(p6x m+(b m)^2) := by
  apply cubic_of_surface_equation
  have hr := product_root_sq m u v hu hv
  have hq : q12 (m^2) ≠ 0 := hr ▸ pow_ne_zero 2 (div_ne_zero (mul_ne_zero hu0 hv0) (by norm_num))
  exact untwist_equation _ _ _ _ _ _ hq hr (t6_equation (m^2))

/-- The explicit fourth abscissa printed in Proposition 4.2. -/
theorem p4x_formula (m : K) :
    p4x m = (49/5)*(m^2-1)*(m^2-81)*(m^2-121)^2*(2*m^2+243) := by
  unfold p4x t4x q2
  field_simp

/-- The explicit fifth abscissa printed in Proposition 4.2. -/
theorem p5x_formula (m : K) :
    p5x m = (49/5)*m⁻¹^2*(m^2-9801)*(m^2-121)*(m^2-81)^2*(3*m^2+242) := by
  unfold p5x t5x q1
  field_simp

/-- The explicit sixth abscissa printed in Proposition 4.2. -/
theorem p6x_formula (m : K) :
    p6x m = 49*(m^2-9801)*(m^2-1)*(m^2-121)^2*(2*m^2+243)/(3*m^2+242) := by
  unfold p6x t6x q12
  by_cases h' : 3*m^2+242 = 0
  · simp only [h', zero_mul, div_zero]
  · field_simp [h']

omit [CharZero K] in
private theorem root_denominator (c q r : K) (hr : r^2=q) (hr0 : r ≠ 0) :
    c/(q*r)=c*r/q^2 := by
  rw [← hr]
  field_simp

/-- The fourth ordinate has no denominator involving v; see Proposition 6.2. -/
theorem p4y_formula (m v : K) (hv : v^2=q2 (m^2)) (hv0 : v ≠ 0)
    (h : 2*m^2+243 ≠ 0) :
    p4y m v = -(686/25)*(m^2-1)*(m^2-36)*(m^2-81)*(m^2-121)^2*twistN (m^2)*v := by
  rw [p4y, root_denominator _ _ _ hv hv0]
  unfold t4y q2
  have h2 : m^2*2+243 ≠ 0 := by simpa only [mul_comm] using h
  field_simp [h2]
  ring

/-- The fifth ordinate uses only powers of 5 and m as denominators. -/
theorem p5y_formula (m u : K) (hu : u^2=q1 (m^2)) (hm : m ≠ 0) (hu0 : u ≠ 0)
    (h : 3*m^2+242 ≠ 0) :
    p5y m u = -(686/25)*m⁻¹^3*(m^2-9801)*(m^2-121)*(4*m^2-1089)*
      (m^2-81)^2*twistN (m^2)*u := by
  have hden : m^2*q1 (m^2)*m*u = m^3*(q1 (m^2)*u) := by ring
  rw [p5y, hden, div_mul_eq_div_div, root_denominator _ _ _ hu hu0]
  unfold t5y q1
  have h2 : m^2*3+242 ≠ 0 := by simpa only [mul_comm] using h
  field_simp [h2, hm]
  ring

/-- The sixth ordinate uses only 3m²+242 as a nonconstant denominator. -/
theorem p6y_formula (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (h : 2*m^2+243 ≠ 0) (h' : 3*m^2+242 ≠ 0) :
    p6y m u v = -343*(m^2-9801)*(m^2-1)*(m^2-99)*(m^2-121)^2*twistN (m^2)*u*v/
      (3*m^2+242)^2 := by
  have hr := product_root_sq m u v hu hv
  rw [p6y, root_denominator _ _ _ hr (div_ne_zero (mul_ne_zero hu0 hv0) (by norm_num))]
  unfold t6y q12
  have h2 : m^2*2+243 ≠ 0 := by simpa only [mul_comm] using h
  have h3 : m^2*3+242 ≠ 0 := by simpa only [mul_comm] using h'
  field_simp [h2, h3]
  ring

/-- The six abscissae, in the printed order. -/
def sixX (m : K) : Fin 6 → K := ![p1x m, p2x m, p3x m, p4x m, p5x m, p6x m]

/-- The six ordinates, with the signs printed in Lemma 2.2 and Proposition 4.2. -/
def sixY (m u v : K) : Fin 6 → K := ![p1y m, p2y m, p3y m, p4y m v, p5y m u, p6y m u v]

/-- Each of the six coordinate pairs satisfies Mathlib's affine equation of X. -/
theorem six_affine_equations (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2))
    (hm : m ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (i : Fin 6) :
    (X m).toAffine.Equation (sixX m i) (sixY m u v i) := by
  apply (E_equation_iff_factored _ _ _ _).2
  fin_cases i
  · exact p1_equation m
  · exact p2_equation m
  · exact p3_equation m
  · exact p4_equation m v hv hv0
  · exact p5_equation m u hu hm hu0
  · exact p6_equation m u v hu hv hu0 hv0

/-- The six sections as elements of the Mathlib elliptic-curve group. -/
def sixPoints (m u v : K) (hu : u^2=q1 (m^2)) (hv : v^2=q2 (m^2))
    (hm : m ≠ 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0) [(X m).IsElliptic] : Fin 6 → (X m).toAffine.Point :=
  fun i => WeierstrassCurve.Affine.Point.mk (six_affine_equations m u v hu hv hm hu0 hv0 i)

end Field

end Z2Z4Rank6
