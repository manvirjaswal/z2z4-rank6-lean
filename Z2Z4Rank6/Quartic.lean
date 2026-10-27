import Z2Z4Rank6.Basic
import Mathlib.Tactic

/-!
# The quartic model in Lemma 4.1

The quartic model and invariants below occur in the proof of Lemma 4.1 of
M. Jaswal, *Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at
least six*, DOI 10.5281/zenodo.23437117.

The explicit maps from the quartic to its printed Weierstrass model are derived
here, making the paper's birational step directly checkable by polynomial identities.
-/

namespace Z2Z4Rank6

def quartic {R : Type*} [CommRing R] (k : R) : R :=
  49*k^4 - 56*k^3 + 514*k^2 - 840*k + 11025

def conicM {K : Type*} [Field K] (k : K) : K :=
  (k^2 - 70*k + 15)/(k^2 - 15)

def conicU {K : Type*} [Field K] (k : K) : K :=
  -5*(7*k^2 - 6*k + 105)/(k^2 - 15)

def conicV {K : Type*} [Field K] (k eta : K) : K :=
  5*eta/(k^2 - 15)

theorem conic_identity {K : Type*} [Field K] (k : K) (hk : k^2 - 15 ≠ 0) :
    (conicU k)^2 = 5*(3*(conicM k)^2 + 242) := by
  unfold conicU conicM
  field_simp
  ring

theorem quartic_conic_identity {K : Type*} [Field K] (k : K) :
    5*(2*(k^2 - 70*k + 15)^2 + 243*(k^2 - 15)^2) = 25*quartic k := by
  unfold quartic
  ring

theorem quartic_to_second_conic {K : Type*} [Field K]
    (k eta : K) (hk : k^2 - 15 ≠ 0) (he : eta^2 = quartic k) :
    (conicV k eta)^2 = 5*(2*(conicM k)^2 + 243) := by
  unfold conicV conicM
  calc
    (5 * eta / (k ^ 2 - 15)) ^ 2 =
        25 * eta^2 / (k^2 - 15)^2 := by simp only [div_pow, mul_pow]; norm_num
    _ = 25 * quartic k / (k^2 - 15)^2 := by rw [he]
    _ = 5 * (2 * ((k ^ 2 - 70*k + 15) / (k ^ 2 - 15))^2 + 243) := by
      unfold quartic
      field_simp
      ring

theorem conic_line {K : Type*} [Field K] (k : K) (hk : k^2 - 15 ≠ 0) :
    conicU k = 35 + k*(conicM k - 1) := by
  unfold conicU conicM
  field_simp
  ring

def quarticX {K : Type*} [Field K] (k eta : K) : K :=
  (7*eta + 49*k^2 - 28*k + 85)/2

def quarticY {K : Type*} [Field K] (k eta : K) : K :=
  (2 - 7*k)*quarticX k eta + 650 - 574*k

theorem quartic_to_ec_equation {K : Type*} [Field K] [CharZero K]
    (k eta : K) (he : eta^2 = quartic k) :
    (quarticY k eta)^2 = (quarticX k eta)^3 + (quarticX k eta)^2 -
      137620*quarticX k eta - 10504000 := by
  simp only [quarticY, quarticX, quartic] at *
  linear_combination (-49*(7*eta + 49*k^2 - 28*k + 249)/8)*he

def ecToK {K : Type*} [Field K] (x y : K) : K :=
  (2*x + 650 - y)/(7*(x + 82))

def ecToEta {K : Type*} [Field K] (x y : K) : K :=
  (2*x - 49*(ecToK x y)^2 + 28*ecToK x y - 85)/7

theorem ec_to_quartic_equation {K : Type*} [Field K] [CharZero K]
    (x y : K) (hx : x + 82 ≠ 0)
    (he : y^2 = x^3 + x^2 - 137620*x - 10504000) :
    (ecToEta x y)^2 = quartic (ecToK x y) := by
  have hid : (ecToEta x y)^2 - quartic (ecToK x y) =
      -4*(y^2 - (x^3 + x^2 - 137620*x - 10504000))/(49*(x+82)) := by
    unfold ecToEta ecToK quartic
    field_simp
    ring
  rw [he, sub_self, mul_zero, zero_div] at hid
  exact sub_eq_zero.mp hid

theorem ec_quartic_x_inverse {K : Type*} [Field K] [CharZero K]
    (x y : K) : quarticX (ecToK x y) (ecToEta x y) = x := by
  unfold quarticX ecToEta
  field_simp
  ring

theorem ec_quartic_y_inverse {K : Type*} [Field K] [CharZero K]
    (x y : K) (hx : x + 82 ≠ 0) :
    quarticY (ecToK x y) (ecToEta x y) = y := by
  rw [quarticY, ec_quartic_x_inverse]
  unfold ecToK
  field_simp
  ring

theorem quartic_invariant_I :
    (12*49*11025 - 3*(-56)*(-840) + 514^2 : ℤ) = 6605776 := by norm_num

theorem quartic_invariant_J :
    (72*49*514*11025 + 9*(-56)*514*(-840) - 27*49*(-840)^2 -
      27*11025*(-56)^2 - 2*514^3 : ℤ) = 18071642752 := by norm_num

theorem quartic_discriminant_value :
    ((4*6605776^3 - 18071642752^2)/27 : ℚ) =
      2^16*3^12*5^2*7^4*11^4 := by norm_num

end Z2Z4Rank6
