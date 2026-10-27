module

public import Z2Z4Rank6.FunctionField
public import Z2Z4Rank6.BaseCurve
public import Z2Z4Rank6.CongruenceSections
public import Common.Elliptic.WeierstrassCoordinates

@[expose] public section

/-!
# The conic base in Proposition 7.1(a)

The rational-function field Q(k), the printed conic parametrization,
and the four sections P₁,P₂,P₃,P₅. Independence is proved by the formal specialization in
ConicSpecialization.
-/

namespace Z2Z4Rank6.ConicBase

open Polynomial

noncomputable section

def mParam {L : Type*} [Field L] (t : L) : L := (t^2-70*t+15)/(t^2-15)
def uParam {L : Type*} [Field L] (t : L) : L := -5*(7*t^2-6*t+105)/(t^2-15)

theorem param_conic {L : Type*} [Field L] (t : L) (ht : t^2-15 ≠ 0) :
    (uParam t)^2=q1 ((mParam t)^2) := by
  unfold mParam uParam q1
  field_simp
  ring

abbrev K := RatFunc ℚ
local instance conicDecidableEq : DecidableEq K := Classical.decEq K

def k : K := RatFunc.X
def m : K := mParam k
def u : K := uParam k

def denominatorPolynomial : ℚ[X] := Polynomial.X^2-15
def mPolynomial : ℚ[X] := Polynomial.X^2-70*Polynomial.X+15
def uPolynomial : ℚ[X] := -5*(7*Polynomial.X^2-6*Polynomial.X+105)

theorem denominator_image :
    algebraMap ℚ[X] K denominatorPolynomial=k^2-15 := by
  simp [denominatorPolynomial,k,RatFunc.algebraMap_X,map_ofNat]

theorem mPolynomial_image : algebraMap ℚ[X] K mPolynomial=k^2-70*k+15 := by
  simp [mPolynomial,k,RatFunc.algebraMap_X,map_ofNat]

theorem uPolynomial_image : algebraMap ℚ[X] K uPolynomial=-5*(7*k^2-6*k+105) := by
  simp [uPolynomial,k,RatFunc.algebraMap_X,map_ofNat]

theorem denominator_ne_zero : k^2-15 ≠ 0 := by
  rw [← denominator_image]
  apply RatFunc.algebraMap_ne_zero
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 2) h
  norm_num [denominatorPolynomial] at hc

theorem conic_relation : u^2=q1 (m^2) := param_conic k denominator_ne_zero

theorem m_not_constant : ¬∃ c : ℚ, m=RatFunc.C c := by
  rintro ⟨c,hc⟩
  have heq : k^2-70*k+15=RatFunc.C c*(k^2-15) :=
    (div_eq_iff denominator_ne_zero).1 hc
  have hp : mPolynomial=Polynomial.C c*denominatorPolynomial := by
    apply RatFunc.algebraMap_injective ℚ
    simpa only [map_mul,RatFunc.algebraMap_C,mPolynomial_image,denominator_image] using heq
  have hcoeff := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  norm_num [mPolynomial,denominatorPolynomial] at hcoeff

theorem m_transcendental : Transcendental ℚ m := by
  convert RatFunc.transcendental_of_ne_C m m_not_constant using 1
  exact Subsingleton.elim _ _

theorem m_ne_zero : m ≠ 0 := by
  intro h
  apply m_not_constant
  exact ⟨0,by simpa using h⟩

theorem m_ne_one : m ≠ 1 := by
  intro h
  apply m_not_constant
  exact ⟨1,by simpa using h⟩

theorem u_ne_zero : u ≠ 0 := by
  intro h
  have hp : uPolynomial=0 := by
    apply RatFunc.algebraMap_injective ℚ
    have hz : -5*(7*k^2-6*k+105)=0 :=
      (div_eq_zero_iff.mp h).resolve_right denominator_ne_zero
    simpa only [uPolynomial_image,map_zero] using hz
  have hc := congrArg (fun p : ℚ[X] => p.coeff 2) hp
  norm_num [uPolynomial,Polynomial.coeff_X] at hc

theorem first_factor_ne_zero : 3*m^2+242 ≠ 0 := by
  intro h
  have heq := conic_relation
  rw [q1,h,mul_zero] at heq
  exact (pow_ne_zero 2 u_ne_zero) heq

theorem parameter_line_relation : (m-1)*k=u-35 := by
  unfold m u mParam uParam
  field_simp [denominator_ne_zero]
  ring

theorem parameter_inverse : k=(u-35)/(m-1) := by
  apply (eq_div_iff (sub_ne_zero.mpr m_ne_one)).2
  simpa only [mul_comm] using parameter_line_relation

/-- The conic coordinates generate exactly Q(k), as the printed inverse map
recovers the transcendental coordinate k. -/
theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,u} : Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,u} : Set K)
  have hm : m ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hk : k ∈ S := by
    rw [parameter_inverse]
    have h35 : (35:K) ∈ S := by simpa only [map_ofNat] using S.algebraMap_mem (35:ℚ)
    exact div_mem (sub_mem hu h35) (sub_mem hm S.one_mem)
  have hx : (RatFunc.X : K) ∈ S := hk
  have hcoeff (r : ℚ) : RatFunc.C r ∈ S := by
    have hC : (RatFunc.C : ℚ →+* K)=algebraMap ℚ K := Subsingleton.elim _ _
    rw [RingHom.congr_fun hC r]
    exact S.algebraMap_mem r
  have hpoly (p : ℚ[X]) : algebraMap ℚ[X] K p ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n r =>
      rw [RatFunc.algebraMap_monomial]
      exact mul_mem (hcoeff r) (pow_mem hx n)
  apply top_unique
  intro z _
  change z ∈ S
  induction z using RatFunc.induction_on with
  | _ p q hq => exact div_mem (hpoly p) (hpoly q)

private def fiberPolynomial : ℚ[X] :=
  a Polynomial.X*b Polynomial.X*((a Polynomial.X)^2-(b Polynomial.X)^2)

private theorem fiberPolynomial_ne_zero : fiberPolynomial ≠ 0 := by
  intro h
  have he := congrArg (Polynomial.eval (2:ℚ)) h
  norm_num [fiberPolynomial,a,b] at he

theorem fiber_product_ne_zero : a m*b m*((a m)^2-(b m)^2) ≠ 0 := by
  have hinj := transcendental_iff_injective.mp m_transcendental
  have he : aeval m fiberPolynomial=a m*b m*((a m)^2-(b m)^2) := by
    simp [fiberPolynomial,a,b,map_ofNat]
  intro h
  apply fiberPolynomial_ne_zero
  apply hinj
  simpa only [map_zero,he] using h

instance genericFiberElliptic : (X m).IsElliptic := by
  have ha := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).1
  have hb := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).2
  have hab := (mul_ne_zero_iff.mp fiber_product_ne_zero).2
  have hd : (X m).Δ=16*(a m)^4*(b m)^4*((a m)^2-(b m)^2)^2 := by
    simp only [X,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  constructor
  rw [isUnit_iff_ne_zero,hd]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 ha))
    (pow_ne_zero 4 hb)) (pow_ne_zero 2 hab)

/-- Columns 1,2,3,5 of the original six-point list. -/
def column : Fin 4 → Fin 6 := ![0,1,2,4]

theorem column_injective : Function.Injective column := by decide +kernel

def fourX {L : Type*} [Field L] (t : L) : Fin 4 → L := ![p1x t,p2x t,p3x t,p5x t]
def fourY {L : Type*} [Field L] (t z : L) : Fin 4 → L := ![p1y t,p2y t,p3y t,p5y t z]

theorem fourX_eq_sixX {L : Type*} [Field L] (t : L) (j : Fin 4) :
    fourX t j=sixX t (column j) := by fin_cases j <;> rfl

theorem fourY_eq_sixY {L : Type*} [Field L] (t z v : L) (j : Fin 4) :
    fourY t z j=sixY t z v (column j) := by fin_cases j <;> rfl

theorem denominator_mul_fourX {L : Type*} [Field L] [CharZero L]
    (t : L) (ht : t ≠ 0) (hA : 3*t^2+242 ≠ 0) (j : Fin 4) :
    sectionDenominator t*fourX t j=sectionXNumerator t (column j) := by
  rw [fourX_eq_sixX]
  exact denominator_mul_sixX t ht hA (column j)

theorem denominator_mul_fourY {L : Type*} [Field L] [CharZero L]
    (t z : L) (hz : z^2=q1 (t^2)) (ht : t ≠ 0) (hz0 : z ≠ 0)
    (hA : 3*t^2+242 ≠ 0) (j : Fin 4) :
    sectionDenominator t*fourY t z j=sectionYNumerator t z 0 (column j) := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · change sectionDenominator t*p5y t z=sectionYNumerator t z 0 4
    rw [p5y_formula t z hz ht hz0 hA]
    dsimp [sectionDenominator,sectionYNumerator]
    field_simp [ht]

theorem four_affine_equations {L : Type*} [Field L] (t z : L)
    (hz : z^2=q1 (t^2)) (ht : t ≠ 0) (hz0 : z ≠ 0) (j : Fin 4) :
    (X t).toAffine.Equation (fourX t j) (fourY t z j) := by
  fin_cases j
  · exact p1_affine_equation t
  · exact p2_affine_equation t
  · exact p3_affine_equation t
  · exact (E_equation_iff_factored _ _ _ _).2 (p5_equation t z hz ht hz0)

def fourPoints {L : Type*} [Field L] (t z : L) (hz : z^2=q1 (t^2))
    (ht : t ≠ 0) (hz0 : z ≠ 0) [(X t).IsElliptic] : Fin 4 → (X t).toAffine.Point :=
  fun j => .mk (four_affine_equations t z hz ht hz0 j)

theorem encode_fourPoints {L : Type*} [Field L] (t z : L) (hz : z^2=q1 (t^2))
    (ht : t ≠ 0) (hz0 : z ≠ 0) [(X t).IsElliptic] (j : Fin 4) :
    Common.WeierstrassCoordinates.encode (fourPoints t z hz ht hz0 j)=
      some (fourX t j,fourY t z j) := rfl

def points : Fin 4 → (X m).toAffine.Point := fourPoints m u conic_relation m_ne_zero u_ne_zero

def baseK : ℚ := 35/41

theorem base_parameters : mParam baseK=baseC0.m ∧ uParam baseK=baseC0.u := by
  norm_num [mParam,uParam,baseK,baseC0]

end
end Z2Z4Rank6.ConicBase
