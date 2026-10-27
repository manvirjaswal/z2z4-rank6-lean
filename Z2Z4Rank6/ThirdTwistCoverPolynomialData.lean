import Z2Z4Rank6.TripleSquareCover
import Mathlib.Algebra.Polynomial.Reverse

/-! Radicands of Q(m,sqrt(q1),sqrt(q2),sqrt(4m²+45)).
Exact rational polynomial certificates prove both chart products separable. -/
namespace Z2Z4Rank6.ThirdTwistCoverPolynomialData
noncomputable section
open Polynomial

def affineRadicand : Fin 3→ℚ[X] :=
  ![15*Polynomial.X^2+1210,10*Polynomial.X^2+1215,4*Polynomial.X^2+45]
def infinityRadicand : Fin 3→ℚ[X] :=
  ![15+1210*Polynomial.X^2,10+1215*Polynomial.X^2,4+45*Polynomial.X^2]
abbrev affineProduct : ℚ[X] := ∏i,affineRadicand i
abbrev infinityProduct : ℚ[X] := ∏i,infinityRadicand i

def affineBezoutA : ℚ[X] := Polynomial.C (4776148/275547410207251875 : ℚ)*Polynomial.X^4+Polynomial.C (3749033626/2479926691865266875 : ℚ)*Polynomial.X^2+Polynomial.C (1/66156750 : ℚ)
def affineBezoutB : ℚ[X] := Polynomial.C (-2388074/826642230621755625 : ℚ)*Polynomial.X^5+Polynomial.C (-2268987461/4959853383730533750 : ℚ)*Polynomial.X^3+Polynomial.C (-3187482457/220437928165801500 : ℚ)*Polynomial.X^1
theorem affine_product_bezout :
    affineBezoutA*affineProduct+affineBezoutB*derivative affineProduct=1 := by
  apply Polynomial.funext
  intro x
  norm_num [affineBezoutA,affineBezoutB,affineProduct,affineRadicand,
    Fin.prod_univ_succ,derivative_add,derivative_mul,derivative_pow]
  ring

theorem affine_product_separable : affineProduct.Separable :=
  ⟨affineBezoutA,affineBezoutB,affine_product_bezout⟩

theorem affine_radicand_natDegree (i : Fin 3) : (affineRadicand i).natDegree=2 := by
  fin_cases i <;> norm_num [affineRadicand] <;> compute_degree!
theorem affine_product_natDegree : affineProduct.natDegree=6 := by
  norm_num [affineProduct,affineRadicand,Fin.prod_univ_succ]
  compute_degree!

def infinityBezoutA : ℚ[X] := Polynomial.C (141315338093787/1666027489000 : ℚ)*Polynomial.X^4+Polynomial.C (44513187953403/8330137445000 : ℚ)*Polynomial.X^2+Polynomial.C (1/600 : ℚ)
def infinityBezoutB : ℚ[X] := Polynomial.C (-47105112697929/3332054978000 : ℚ)*Polynomial.X^5+Polynomial.C (-46871342660883/33320549780000 : ℚ)*Polynomial.X^3+Polynomial.C (-667372970053/49980824670000 : ℚ)*Polynomial.X^1
theorem infinity_product_bezout :
    infinityBezoutA*infinityProduct+infinityBezoutB*derivative infinityProduct=1 := by
  apply Polynomial.funext
  intro x
  norm_num [infinityBezoutA,infinityBezoutB,infinityProduct,infinityRadicand,
    Fin.prod_univ_succ,derivative_add,derivative_mul,derivative_pow]
  ring

theorem infinity_product_separable : infinityProduct.Separable :=
  ⟨infinityBezoutA,infinityBezoutB,infinity_product_bezout⟩

theorem infinity_radicand_natDegree (i : Fin 3) : (infinityRadicand i).natDegree=2 := by
  fin_cases i <;> norm_num [infinityRadicand] <;> compute_degree!
theorem infinity_product_natDegree : infinityProduct.natDegree=6 := by
  norm_num [infinityProduct,infinityRadicand,Fin.prod_univ_succ]
  compute_degree!

end
end Z2Z4Rank6.ThirdTwistCoverPolynomialData
