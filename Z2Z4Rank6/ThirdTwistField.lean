import Z2Z4Rank6.FunctionField
import Z2Z4Rank6.SecondFunctionField

/-! The fields where the third twist 4m²+45 becomes a square,
with one or both of the original two square roots. -/

namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open Polynomial
set_option maxHeartbeats 400000

abbrev Base := FunctionField.Base
def thirdPolynomial : ℚ[X] := 4*Polynomial.X^2+45
def d3 : Base := 4*RatFunc.X^2+45

theorem thirdPolynomial_image : algebraMap ℚ[X] Base thirdPolynomial=d3 := by
  simp [thirdPolynomial,d3,RatFunc.algebraMap_X,map_ofNat]

theorem firstPolynomial_image :
    algebraMap ℚ[X] Base FunctionField.firstPolynomial=FunctionField.d1 := by
  simp [FunctionField.firstPolynomial,FunctionField.d1,q1,RatFunc.algebraMap_X,map_ofNat]

theorem secondPolynomial_image :
    algebraMap ℚ[X] Base FunctionField.secondPolynomial=FunctionField.d2 := by
  simp [FunctionField.secondPolynomial,FunctionField.d2,q2,RatFunc.algebraMap_X,map_ofNat]

theorem first_leadingCoeff : FunctionField.firstPolynomial.leadingCoeff=15 := by
  have he : FunctionField.firstPolynomial=C 15*Polynomial.X^2+C 0*Polynomial.X+C 1210 := by
    norm_num only [FunctionField.firstPolynomial,Polynomial.C_ofNat,Polynomial.C_0]
    ring
  rw [he,Polynomial.leadingCoeff_quadratic (by norm_num)]

theorem second_leadingCoeff : FunctionField.secondPolynomial.leadingCoeff=10 := by
  have he : FunctionField.secondPolynomial=C 10*Polynomial.X^2+C 0*Polynomial.X+C 1215 := by
    norm_num only [FunctionField.secondPolynomial,Polynomial.C_ofNat,Polynomial.C_0]
    ring
  rw [he,Polynomial.leadingCoeff_quadratic (by norm_num)]

theorem third_leadingCoeff : thirdPolynomial.leadingCoeff=4 := by
  have he : thirdPolynomial=C 4*Polynomial.X^2+C 0*Polynomial.X+C 45 := by
    norm_num only [thirdPolynomial,Polynomial.C_ofNat,Polynomial.C_0]
    ring
  rw [he,Polynomial.leadingCoeff_quadratic (by norm_num)]

theorem not_isSquare_fraction_of_eval {F : Type*} [Field F]
    (p : F[X]) (r : F) (hp : ¬IsSquare (p.eval r)) :
    ¬IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨z,hz⟩
  have hint : IsIntegral F[X] (z^2) := by
    rw [sq,←hz]
    exact isIntegral_algebraMap
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=F[X]) (by decide : 0<(2 : ℕ)) hint
  have he : p=a*a := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_mul,ha] using hz
  apply hp
  refine ⟨a.eval r,?_⟩
  rw [he,Polynomial.eval_mul]

theorem d3_not_isSquare : ¬IsSquare d3 := by
  rw [←thirdPolynomial_image]
  exact not_isSquare_fraction_of_eval thirdPolynomial 0 (by norm_num [thirdPolynomial])

theorem d1_mul_d3_not_isSquare : ¬IsSquare (FunctionField.d1*d3) := by
  rw [←firstPolynomial_image,←thirdPolynomial_image,←map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [Polynomial.leadingCoeff_mul,first_leadingCoeff,third_leadingCoeff]
  norm_num

theorem d2_mul_d3_not_isSquare : ¬IsSquare (FunctionField.d2*d3) := by
  rw [←secondPolynomial_image,←thirdPolynomial_image,←map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [Polynomial.leadingCoeff_mul,second_leadingCoeff,third_leadingCoeff]
  norm_num

theorem d1_mul_d2_mul_d3_not_isSquare : ¬IsSquare (FunctionField.d1*(FunctionField.d2*d3)) := by
  rw [←firstPolynomial_image,←secondPolynomial_image,
    ←thirdPolynomial_image,←map_mul,←map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  simp only [Polynomial.leadingCoeff_mul,first_leadingCoeff,second_leadingCoeff,third_leadingCoeff]
  norm_num

def d3Old : FunctionField.K := algebraMap Base FunctionField.K d3

theorem d3Old_not_isSquare : ¬IsSquare d3Old :=
  SecondFunctionField.not_isSquare_in_biquadratic FunctionField.d1 FunctionField.d2 d3
    FunctionField.d1_not_isSquare d3_not_isSquare d1_mul_d3_not_isSquare
    d2_mul_d3_not_isSquare d1_mul_d2_mul_d3_not_isSquare

instance d3Old_nonsquare : Fact (¬IsSquare d3Old) := ⟨d3Old_not_isSquare⟩

abbrev K := QuadraticAlgebra FunctionField.K d3Old 0
def m : K := algebraMap FunctionField.K K FunctionField.m
def u : K := algebraMap FunctionField.K K FunctionField.u
def v : K := algebraMap FunctionField.K K FunctionField.v
def w : K := QuadraticAlgebra.omega

theorem m_eq_base : m=algebraMap Base K RatFunc.X := by
  rw [m,FunctionField.m,←IsScalarTower.algebraMap_apply Base FunctionField.K K]

theorem u_sq : u^2=5*(3*m^2+242) := by
  rw [u,←map_pow,FunctionField.u_sq]
  simp [m,map_ofNat]

theorem v_sq : v^2=5*(2*m^2+243) := by
  rw [v,←map_pow,FunctionField.v_sq]
  simp [m,map_ofNat]

theorem w_sq : w^2=4*m^2+45 := by
  have hroot : w^2=algebraMap FunctionField.K K d3Old := by
    rw [w,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [hroot]
  change algebraMap FunctionField.K K (algebraMap Base FunctionField.K d3)=_
  rw [←IsScalarTower.algebraMap_apply Base FunctionField.K K]
  simp [d3,m_eq_base,map_ofNat]

theorem finrank_eq_eight : Module.finrank Base K=8 := by
  rw [←Module.finrank_mul_finrank Base FunctionField.K K,
    FunctionField.finrank_eq_four,QuadraticAlgebra.finrank_eq_two]

def d3First : FunctionField.First := algebraMap Base FunctionField.First d3
theorem d3First_not_isSquare : ¬IsSquare d3First :=
  FunctionField.not_isSquare_in_quadratic FunctionField.d1 d3
    d3_not_isSquare d1_mul_d3_not_isSquare
instance d3First_nonsquare : Fact (¬IsSquare d3First) := ⟨d3First_not_isSquare⟩
abbrev PairOne := QuadraticAlgebra FunctionField.First d3First 0

instance d2_nonsquare : Fact (¬IsSquare FunctionField.d2) := ⟨FunctionField.d2_not_isSquare⟩
abbrev PairTwoFirst := QuadraticAlgebra Base FunctionField.d2 0
def d3PairTwoFirst : PairTwoFirst := algebraMap Base PairTwoFirst d3
theorem d3PairTwoFirst_not_isSquare : ¬IsSquare d3PairTwoFirst :=
  FunctionField.not_isSquare_in_quadratic FunctionField.d2 d3
    d3_not_isSquare d2_mul_d3_not_isSquare
instance d3PairTwoFirst_nonsquare : Fact (¬IsSquare d3PairTwoFirst) := ⟨d3PairTwoFirst_not_isSquare⟩
abbrev PairTwo := QuadraticAlgebra PairTwoFirst d3PairTwoFirst 0

theorem pairOne_finrank : Module.finrank Base PairOne=4 := by
  rw [←Module.finrank_mul_finrank Base FunctionField.First PairOne,
    FunctionField.first_finrank,QuadraticAlgebra.finrank_eq_two]

theorem pairTwo_finrank : Module.finrank Base PairTwo=4 := by
  rw [←Module.finrank_mul_finrank Base PairTwoFirst PairTwo,
    QuadraticAlgebra.finrank_eq_two,QuadraticAlgebra.finrank_eq_two]

namespace PairOne

def m : PairOne := algebraMap Base PairOne RatFunc.X
def u : PairOne := algebraMap FunctionField.First PairOne QuadraticAlgebra.omega
def w : PairOne := QuadraticAlgebra.omega

theorem u_sq : u^2=5*(3*m^2+242) := by
  have hr : (QuadraticAlgebra.omega : FunctionField.First)^2=
      algebraMap Base FunctionField.First FunctionField.d1 := by
    rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [u,←map_pow,hr,←IsScalarTower.algebraMap_apply Base FunctionField.First PairOne]
  simp [FunctionField.d1,q1,m,map_ofNat]

theorem w_sq : w^2=4*m^2+45 := by
  have hr : w^2=algebraMap FunctionField.First PairOne d3First := by
    rw [w,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [hr]
  change algebraMap FunctionField.First PairOne (algebraMap Base FunctionField.First d3)=_
  rw [←IsScalarTower.algebraMap_apply Base FunctionField.First PairOne]
  simp [d3,m,map_ofNat]

end PairOne

namespace PairTwo

def m : PairTwo := algebraMap Base PairTwo RatFunc.X
def u : PairTwo := algebraMap PairTwoFirst PairTwo QuadraticAlgebra.omega
def w : PairTwo := QuadraticAlgebra.omega

theorem u_sq : u^2=5*(2*m^2+243) := by
  have hr : (QuadraticAlgebra.omega : PairTwoFirst)^2=
      algebraMap Base PairTwoFirst FunctionField.d2 := by
    rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [u,←map_pow,hr,←IsScalarTower.algebraMap_apply Base PairTwoFirst PairTwo]
  simp [FunctionField.d2,q2,m,map_ofNat]

theorem w_sq : w^2=4*m^2+45 := by
  have hr : w^2=algebraMap PairTwoFirst PairTwo d3PairTwoFirst := by
    rw [w,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [hr]
  change algebraMap PairTwoFirst PairTwo (algebraMap Base PairTwoFirst d3)=_
  rw [←IsScalarTower.algebraMap_apply Base PairTwoFirst PairTwo]
  simp [d3,m,map_ofNat]

end PairTwo

end
end Z2Z4Rank6.ThirdTwistField
