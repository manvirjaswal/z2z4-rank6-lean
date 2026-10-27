module

public import Z2Z4Rank6.GFunctionField
public import Common.Elliptic.WeierstrassCoordinates

@[expose] public section

/-!
# The two involution sections over G

The transformation m'=(η−98m)/(99−m²), δ=(99−m²)/(14m') in
Proposition 7.2(b). Polynomial certificates prove its parameter identities;
the five coordinates are points of X over the quadratic field.
-/

namespace Z2Z4Rank6.GFunctionField

noncomputable section

def mPrime {L : Type*} [Field L] (t z : L) : L := (z-98*t)/(99-t^2)
def delta {L : Type*} [Field L] (t z : L) : L := (99-t^2)/(14*mPrime t z)

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
theorem mPrime_ne_zero (t z : L) (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    mPrime t z ≠ 0 := div_ne_zero hz hd

theorem delta_ne_zero (t z : L) (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    delta t z ≠ 0 := div_ne_zero hd (mul_ne_zero (by norm_num) (mPrime_ne_zero t z hd hz))

theorem delta_formula (t z : L) (hd : 99-t^2 ≠ 0) (_hz : z-98*t ≠ 0) :
    delta t z=(99-t^2)^2/(14*(z-98*t)) := by
  unfold delta mPrime
  field_simp

def aCertificate (t z : L) : L :=
  -99*t^4-9800*t^3+100*t^2*z+48414*t^2-392*t*z+970200*t+z^2-9900*z-970299

def bCertificate (t z : L) : L :=
  99*t^4-9800*t^3+100*t^2*z-48414*t^2+392*t*z+970200*t-z^2-9900*z+970299

theorem a_transform_cleared (t z : L) (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    28*(z-98*t)^2*((delta t z)^2*a (mPrime t z)-a t)=
      (z^2-h t)*aCertificate t z := by
  rw [delta_formula t z hd hz]
  unfold mPrime a h aCertificate
  field_simp
  ring

theorem b_transform_cleared (t z : L) (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    28*(z-98*t)^2*((delta t z)^2*b (mPrime t z)-b t)=
      (z^2-h t)*bCertificate t z := by
  rw [delta_formula t z hd hz]
  unfold mPrime b h bCertificate
  field_simp
  ring

theorem a_transform (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) : (delta t z)^2*a (mPrime t z)=a t := by
  have hc := a_transform_cleared t z hd hz
  rw [he,sub_self,zero_mul] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)))

theorem b_transform (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) : (delta t z)^2*b (mPrime t z)=b t := by
  have hc := b_transform_cleared t z hd hz
  rw [he,sub_self,zero_mul] at hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)))

omit [CharZero L] in
theorem tau_cleared (t z : L) (hd : 99-t^2 ≠ 0) :
    (t^2-99)*((99-(mPrime t z)^2)*(99-t^2)-196*t*mPrime t z)=z^2-h t := by
  unfold mPrime h
  field_simp
  ring

theorem tau_inversion (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    (99-(mPrime t z)^2)/(14*mPrime t z)=14*t/(99-t^2) := by
  have hc := tau_cleared t z hd
  rw [he,sub_self] at hc
  have hd' : t^2-99 ≠ 0 := by intro hh; apply hd; linear_combination -hh
  have hr := (mul_eq_zero.mp hc).resolve_left hd'
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) (mPrime_ne_zero t z hd hz)) hd).2
  linear_combination hr

/-- The printed transformation is a Weierstrass variable change. -/
theorem transform_curve (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) :
    scalingChange (Units.mk0 ((delta t z)^2)
      (pow_ne_zero 2 (delta_ne_zero t z hd hz))) • X (mPrime t z)=X t := by
  rw [X,scalingChange_E]
  change E ((delta t z)^2*a (mPrime t z)) ((delta t z)^2*b (mPrime t z))=X t
  rw [a_transform t z he hd hz,b_transform t z he hd hz]
  rfl

theorem transformed_equation (t z x y : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0)
    (hp : y^2=x*(x+(a (mPrime t z))^2)*(x+(b (mPrime t z))^2)) :
    ((delta t z)^6*y)^2=((delta t z)^4*x)*
      ((delta t z)^4*x+(a t)^2)*((delta t z)^4*x+(b t)^2) := by
  rw [← a_transform t z he hd hz,← b_transform t z he hd hz]
  calc
    _=(delta t z)^12*y^2 := by ring
    _=_ := by rw [hp]; ring

def fiveX (t z : L) : Fin 5 → L :=
  ![p1x t,p2x t,p3x t,(delta t z)^4*p2x (mPrime t z),(delta t z)^4*p3x (mPrime t z)]

def fiveY (t z : L) : Fin 5 → L :=
  ![p1y t,p2y t,p3y t,(delta t z)^6*p2y (mPrime t z),(delta t z)^6*p3y (mPrime t z)]

theorem five_affine_equations (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) (j : Fin 5) :
    (X t).toAffine.Equation (fiveX t z j) (fiveY t z j) := by
  fin_cases j
  · exact p1_affine_equation t
  · exact p2_affine_equation t
  · exact p3_affine_equation t
  · exact (E_equation_iff_factored _ _ _ _).2
      (transformed_equation t z _ _ he hd hz (p2_equation (mPrime t z)))
  · exact (E_equation_iff_factored _ _ _ _).2
      (transformed_equation t z _ _ he hd hz (p3_equation (mPrime t z)))

def fivePoints (t z : L) (he : z^2=h t) (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0)
    [(X t).IsElliptic] : Fin 5 → (X t).toAffine.Point :=
  fun j => .mk (five_affine_equations t z he hd hz j)

theorem encode_fivePoints (t z : L) (he : z^2=h t)
    (hd : 99-t^2 ≠ 0) (hz : z-98*t ≠ 0) [(X t).IsElliptic] (j : Fin 5) :
    Common.WeierstrassCoordinates.encode (fivePoints t z he hd hz j)=
      some (fiveX t z j,fiveY t z j) := rfl

def points : Fin 5 → (X m).toAffine.Point :=
  fivePoints m eta eta_sq chart_denominator_ne_zero chart_numerator_ne_zero

end
end Z2Z4Rank6.GFunctionField
