import Z2Z4Rank6.TorsionSquareLiftData
import Z2Z4Rank6.HeightInvariantForms
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Radicand data for the signed triple-square torsion covers

Jaswal, DOI 10.5281/zenodo.23437117, the torsion covers used in Lemma 6.1
and Theorem 1.2(c). Both affine charts use the printed polynomials.
The product in each chart is separable of degree 12. An exact rational Euclidean certificate for the
infinity product's core is checked by polynomial arithmetic.
-/
namespace Z2Z4Rank6.TorsionCoverPolynomialData
open Polynomial
open TorsionHyperelliptic
noncomputable section

def affineRadicand (ε : Bool) : Fin 3 → ℚ[X] :=
  ![15*Polynomial.X^2+1210,10*Polynomial.X^2+1215,
    C (sign ε)*a Polynomial.X*b Polynomial.X]

def infinityRadicand (ε : Bool) : Fin 3 → ℚ[X] :=
  ![15+1210*Polynomial.X^2,10+1215*Polynomial.X^2,
    C (sign ε)*HeightInvariantForms.binaryA Polynomial.X 1*
      HeightInvariantForms.binaryB Polynomial.X 1]

abbrev affineProduct (ε : Bool) : ℚ[X] := ∏i : Fin 3,affineRadicand ε i
abbrev infinityProduct (ε : Bool) : ℚ[X] := ∏i : Fin 3,infinityRadicand ε i

theorem affine_product_eq_H (ε : Bool) : affineProduct ε=H ε := by
  rw [affineProduct,Fin.prod_univ_three]
  change (15*Polynomial.X^2+1210)*(10*Polynomial.X^2+1215)*
    (C (sign ε)*a Polynomial.X*b Polynomial.X)=H ε
  unfold H q1 q2
  ring

def infinityCore : ℚ[X] :=
  (3+242*Polynomial.X^2)*(2+243*Polynomial.X^2)*
    (1-Polynomial.X^2)*(1-81*Polynomial.X^2)*(1-121*Polynomial.X^2)*
    (1-9801*Polynomial.X^2)

theorem infinity_product_factor (ε : Bool) :
    infinityProduct ε=C (-1225*sign ε)*infinityCore := by
  rw [infinityProduct,Fin.prod_univ_three]
  change (15+1210*Polynomial.X^2)*(10+1215*Polynomial.X^2)*
    (C (sign ε)*HeightInvariantForms.binaryA Polynomial.X 1*
      HeightInvariantForms.binaryB Polynomial.X 1)=C (-1225*sign ε)*infinityCore
  unfold infinityCore HeightInvariantForms.binaryA HeightInvariantForms.binaryB
  simp only [map_mul,map_neg,map_ofNat]
  ring

def infinityBezoutA : ℚ[X] := Polynomial.C (1/6 : ℚ)*Polynomial.X^0+Polynomial.C (-108152401220003772425720248087/75014018653944384000000000000 : ℚ)*Polynomial.X^2+Polynomial.C (-265760141842623366009429342682109/25004672884648128000000000000 : ℚ)*Polynomial.X^4+Polynomial.C (273109521371483122798610071210167/8334890961549376000000000000 : ℚ)*Polynomial.X^6+Polynomial.C (668247187955784376018876223206443147/8334890961549376000000000000 : ℚ)*Polynomial.X^8+Polynomial.C (-200529262863595128548197374843881817/2083722740387344000000000000 : ℚ)*Polynomial.X^10

def infinityBezoutB : ℚ[X] := Polynomial.C (-695187240970453893299018439/8334890961549376000000000000 : ℚ)*Polynomial.X^1+Polynomial.C (8702136848077910069776207277/30005607461577753600000000000 : ℚ)*Polynomial.X^3+Polynomial.C (53169629146818078519143241349771/30005607461577753600000000000 : ℚ)*Polynomial.X^5+Polynomial.C (-11652476868518307343998117501519/3333956384619750400000000000 : ℚ)*Polynomial.X^7+Polynomial.C (-26731490997011898683542151248648353/3333956384619750400000000000 : ℚ)*Polynomial.X^9+Polynomial.C (66843087621198376182732458281293939/8334890961549376000000000000 : ℚ)*Polynomial.X^11

/-- Exact rational Bezout certificate for the infinity-chart core. -/
theorem infinity_core_bezout :
    infinityBezoutA*infinityCore+infinityBezoutB*derivative infinityCore=1 := by
  apply Polynomial.funext
  intro x
  norm_num [infinityBezoutA,infinityBezoutB,infinityCore,derivative_mul,derivative_pow]
  ring

theorem infinity_core_separable : infinityCore.Separable :=
  ⟨infinityBezoutA,infinityBezoutB,infinity_core_bezout⟩

theorem affine_product_separable (ε : Bool) : (affineProduct ε).Separable := by
  rw [affine_product_eq_H]
  exact H_separable ε

theorem infinity_product_separable (ε : Bool) : (infinityProduct ε).Separable := by
  rw [infinity_product_factor]
  apply infinity_core_separable.unit_mul
  apply isUnit_C.mpr
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (sign_ne_zero ε))

theorem affine_product_bezout (ε : Bool) :
    ∃A B : ℚ[X],A*affineProduct ε+B*derivative (affineProduct ε)=1 :=
  affine_product_separable ε

theorem infinity_product_bezout (ε : Bool) :
    ∃A B : ℚ[X],A*infinityProduct ε+B*derivative (infinityProduct ε)=1 :=
  infinity_product_separable ε

theorem affine_product_natDegree (ε : Bool) : (affineProduct ε).natDegree=12 := by
  rw [affine_product_eq_H,H_natDegree]

theorem infinity_product_natDegree (ε : Bool) : (infinityProduct ε).natDegree=12 := by
  cases ε <;> rw [infinity_product_factor] <;>
    unfold sign infinityCore <;> norm_num <;> compute_degree!

theorem affine_product_squarefree (ε : Bool) : Squarefree (affineProduct ε) :=
  (affine_product_separable ε).squarefree

theorem infinity_product_squarefree (ε : Bool) : Squarefree (infinityProduct ε) :=
  (infinity_product_separable ε).squarefree

theorem affine_radicand_natDegree (ε : Bool) (i : Fin 3) :
    (affineRadicand ε i).natDegree=![2,2,8] i := by
  cases ε <;> fin_cases i <;>
    norm_num [affineRadicand,sign,a,b] <;> compute_degree!

theorem infinity_radicand_natDegree (ε : Bool) (i : Fin 3) :
    (infinityRadicand ε i).natDegree=![2,2,8] i := by
  cases ε <;> fin_cases i <;>
    norm_num [infinityRadicand,sign,HeightInvariantForms.binaryA,
      HeightInvariantForms.binaryB] <;> compute_degree!

theorem infinity_product_eval_zero (ε : Bool) :
    (infinityProduct ε).eval 0= -7350*sign ε := by
  rw [infinity_product_factor]
  simp [infinityCore]
  ring

theorem infinity_product_eval_zero_ne (ε : Bool) : (infinityProduct ε).eval 0≠0 := by
  rw [infinity_product_eval_zero]
  exact mul_ne_zero (by norm_num) (sign_ne_zero ε)

theorem affine_product_eval_zero_ne (ε : Bool) : (affineProduct ε).eval 0≠0 := by
  rw [affine_product_eq_H,H_factor]
  cases ε <;> norm_num [sign,core]

end
end Z2Z4Rank6.TorsionCoverPolynomialData

