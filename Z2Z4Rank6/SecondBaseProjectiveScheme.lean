import Common.Elliptic.QuadricIntersectionModel
import Z2Z4Rank6.SecondFamily

/-!
# The projective second base

Theorem 8.1(a) of Jaswal, DOI 10.5281/zenodo.23437117. With homogeneous
coordinates (M,U,V,Z), U=1089s₂ and V=1089s₃, the two equations below are
exactly s₂²=29(s₁²−β), s₃²=−29β(s₁²−γ) on Z=1, with s₁=M/Z.
The auxiliary printed coordinate W is s₁². This invertible rational scaling
does not drop any of the three square roots or change the base curve.
-/

namespace Z2Z4Rank6.SecondBaseProjectiveScheme
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Classical
set_option maxHeartbeats 1200000

def model : QuadricIntersectionModel.Model where
  polynomial := ![MvPolynomial.X 1^2-C 34391709*MvPolynomial.X 0^2+C 751709*MvPolynomial.X 3^2,
    MvPolynomial.X 2^2+C 751709*MvPolynomial.X 0^2-C 3779309*MvPolynomial.X 3^2]
  homogeneous := by
    intro i
    fin_cases i
    · exact (((isHomogeneous_X ℚ (1:Fin 4)).pow 2).sub
        (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul 34391709)).add
        (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul 751709)
    · exact (((isHomogeneous_X ℚ (2:Fin 4)).pow 2).add
        (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul 751709)).sub
        (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul 3779309)

abbrev PolynomialRing := QuadricIntersectionModel.PolynomialRing
abbrev relation := model.polynomial
abbrev definingIdeal := QuadricIntersectionModel.definingIdeal model
abbrev CoordinateRing := QuadricIntersectionModel.CoordinateRing model
abbrev grading := QuadricIntersectionModel.grading model
abbrev scheme := QuadricIntersectionModel.scheme model
abbrev structureMap := QuadricIntersectionModel.structureMap model

def coordinate (i : Fin 4) : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X i)
abbrev m := coordinate 0
abbrev u := coordinate 1
abbrev v := coordinate 2
abbrev z := coordinate 3

theorem coordinate_degree (i : Fin 4) : coordinate i ∈ grading 1 :=
  ⟨MvPolynomial.X i,isHomogeneous_X ℚ i,rfl⟩

theorem coordinate_relation (i : Fin 2) :
    Ideal.Quotient.mk definingIdeal (relation i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem u_sq : u^2=34391709*m^2-751709*z^2 := by
  have h := coordinate_relation 0
  change Ideal.Quotient.mk definingIdeal
    (MvPolynomial.X 1^2-C 34391709*MvPolynomial.X 0^2+C 751709*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_add,map_pow,map_mul] at h
  change u^2-34391709*m^2+751709*z^2=0 at h
  linear_combination h

theorem v_sq : v^2= -751709*m^2+3779309*z^2 := by
  have h := coordinate_relation 1
  change Ideal.Quotient.mk definingIdeal
    (MvPolynomial.X 2^2+C 751709*MvPolynomial.X 0^2-C 3779309*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_add,map_pow,map_mul] at h
  change v^2+751709*m^2-3779309*z^2=0 at h
  linear_combination h

@[simp] private theorem pderiv_two (i : Fin 4) :
    MvPolynomial.pderiv i (2 : PolynomialRing)=0 := by
  rw [show (2 : PolynomialRing)=1+1 by ring]
  simp

theorem hessian_zero : QuadricIntersectionModel.hessian model 0=
    Matrix.diagonal ![-68783418,2,0,1503418] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Matrix.diagonal]

theorem hessian_one : QuadricIntersectionModel.hessian model 1=
    Matrix.diagonal ![1503418,0,2,-7558618] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Matrix.diagonal]

theorem pencilPolynomial_eq : QuadricIntersectionModel.pencilPolynomial model=
    (-68783418*Polynomial.X+1503418)*(2*Polynomial.X)*2*
      (1503418*Polynomial.X-7558618) := by
  have hm : (fun i j => Polynomial.C (QuadricIntersectionModel.hessian model 0 i j)*Polynomial.X+
      Polynomial.C (QuadricIntersectionModel.hessian model 1 i j))=
      Matrix.diagonal ![-68783418*Polynomial.X+1503418,2*Polynomial.X,2,
        1503418*Polynomial.X-7558618] := by
    rw [hessian_zero,hessian_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal,Polynomial.C_ofNat,Polynomial.coeff_neg,sub_eq_add_neg]
  rw [QuadricIntersectionModel.pencilPolynomial,hm,Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]
  ring

theorem pencilPolynomial_expanded : QuadricIntersectionModel.pencilPolynomial model=
    Polynomial.C (-413640914890896)*Polynomial.X^3+
      Polynomial.C 2088671388316192*Polynomial.X^2-
      Polynomial.C 45455049425296*Polynomial.X := by
  rw [pencilPolynomial_eq]
  norm_num only [map_neg,map_ofNat]
  ring

theorem discriminant_ne_zero : QuadricIntersectionModel.discriminant model≠0 := by
  norm_num [QuadricIntersectionModel.discriminant,QuadricIntersectionModel.c4,
    QuadricIntersectionModel.c6,QuadricIntersectionModel.invariantI,
    QuadricIntersectionModel.invariantJ,pencilPolynomial_expanded,
    Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow,Polynomial.coeff_X]

/-- The second base is a smooth proper geometrically integral
curve of genus one. The hypothesis is CFS Theorem 2.8(ii) for pairs of quadrics; its discriminant
condition is proved above. -/
theorem genus_one (h : QuadricIntersectionModel.CFSTheorem28ii) :
    AlgebraicGeometry.RationalCurveGenus.IsSmoothProperGenusOne scheme structureMap :=
  QuadricIntersectionModel.genus_one h model discriminant_ne_zero

end
end Z2Z4Rank6.SecondBaseProjectiveScheme
