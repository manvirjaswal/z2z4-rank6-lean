import Z2Z4Rank6.SecondTorsionSquareLiftData
import Mathlib.Algebra.Polynomial.Reverse

/-! Signed second torsion-cover radicands. Jaswal, Theorem 8.1(c),
DOI 10.5281/zenodo.23437117. The eight branch roots are explicitly rational. -/
namespace Z2Z4Rank6.SecondTorsionCoverPolynomialData
open Polynomial SecondFamily
noncomputable section
abbrev sign := TorsionHyperelliptic.sign

def affineRadicand (ε : Bool) : Fin 3 → ℚ[X] :=
  ![29*(Polynomial.X^2-C beta),C (-29*beta)*(Polynomial.X^2-C gamma),
    -C (sign ε)*(Polynomial.X^2-1)*(Polynomial.X^2-C (lambda^2))]
def infinityRadicand (ε : Bool) : Fin 3 → ℚ[X] :=
  ![29*(1-C beta*Polynomial.X^2),C (-29*beta)*(1-C gamma*Polynomial.X^2),
    -C (sign ε)*(1-Polynomial.X^2)*(1-C (lambda^2)*Polynomial.X^2)]
abbrev affineProduct (ε : Bool) : ℚ[X] := ∏i : Fin 3,affineRadicand ε i
abbrev infinityProduct (ε : Bool) : ℚ[X] := ∏i : Fin 3,infinityRadicand ε i

def roots : Fin 8 → ℚ := ![161/1089,-161/1089,361/161,-361/161,1,-1,361/1089,-361/1089]
def infinityRoots : Fin 8 → ℚ := ![1089/161,-1089/161,161/361,-161/361,1,-1,1089/361,-1089/361]
def core : ℚ[X] := ∏i : Fin 8,(Polynomial.X-C (roots i))
def infinityCore : ℚ[X] := ∏i : Fin 8,(Polynomial.X-C (infinityRoots i))
theorem roots_injective : Function.Injective roots := by decide +kernel
theorem infinityRoots_injective : Function.Injective infinityRoots := by decide +kernel
theorem core_separable : core.Separable := Polynomial.separable_prod_X_sub_C_iff.mpr roots_injective
theorem infinityCore_separable : infinityCore.Separable := Polynomial.separable_prod_X_sub_C_iff.mpr infinityRoots_injective

theorem affine_product_factor (ε : Bool) : affineProduct ε=C (841*beta*sign ε)*core := by
  apply Polynomial.funext
  intro x
  norm_num [affineProduct,affineRadicand,core,roots,Fin.prod_univ_succ,beta,gamma,lambda]
  ring

theorem infinity_product_factor (ε : Bool) : infinityProduct ε=C (841*beta*lambda^4*sign ε)*infinityCore := by
  apply Polynomial.funext
  intro x
  norm_num [infinityProduct,infinityRadicand,infinityCore,infinityRoots,Fin.prod_univ_succ,beta,gamma,lambda]
  ring

theorem affine_product_separable (ε : Bool) : (affineProduct ε).Separable := by
  rw [affine_product_factor]
  apply core_separable.unit_mul
  apply isUnit_C.mpr
  apply isUnit_iff_ne_zero.mpr
  exact mul_ne_zero (by norm_num [beta]) (TorsionHyperelliptic.sign_ne_zero ε)
theorem infinity_product_separable (ε : Bool) : (infinityProduct ε).Separable := by
  rw [infinity_product_factor]
  apply infinityCore_separable.unit_mul
  apply isUnit_C.mpr
  apply isUnit_iff_ne_zero.mpr
  exact mul_ne_zero (by norm_num [beta,lambda]) (TorsionHyperelliptic.sign_ne_zero ε)
theorem affine_product_bezout (ε : Bool) : ∃A B : ℚ[X],A*affineProduct ε+B*derivative (affineProduct ε)=1 := affine_product_separable ε
theorem infinity_product_bezout (ε : Bool) : ∃A B : ℚ[X],A*infinityProduct ε+B*derivative (infinityProduct ε)=1 := infinity_product_separable ε

theorem affine_radicand_natDegree (ε : Bool) (i : Fin 3) : (affineRadicand ε i).natDegree=![2,2,4] i := by
  cases ε <;> fin_cases i <;> norm_num [affineRadicand,sign,TorsionHyperelliptic.sign,beta,gamma,lambda] <;> compute_degree!
theorem infinity_radicand_natDegree (ε : Bool) (i : Fin 3) : (infinityRadicand ε i).natDegree=![2,2,4] i := by
  cases ε <;> fin_cases i <;> norm_num [infinityRadicand,sign,TorsionHyperelliptic.sign,beta,gamma,lambda] <;> compute_degree!
theorem affine_product_natDegree (ε : Bool) : (affineProduct ε).natDegree=8 := by
  cases ε <;> rw [affineProduct,Fin.prod_univ_three] <;> norm_num [affineRadicand,sign,TorsionHyperelliptic.sign,beta,gamma,lambda] <;> compute_degree!
theorem infinity_product_natDegree (ε : Bool) : (infinityProduct ε).natDegree=8 := by
  cases ε <;> rw [infinityProduct,Fin.prod_univ_three] <;> norm_num [infinityRadicand,sign,TorsionHyperelliptic.sign,beta,gamma,lambda] <;> compute_degree!
end
end Z2Z4Rank6.SecondTorsionCoverPolynomialData
