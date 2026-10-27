import Common.Elliptic.QuadricIntersectionModel
import Common.AlgebraicGeometry.ProjValuedPoint
import Z2Z4Rank6.ThirdTwistField

/-!
# The two genus-one bases involving the third twist

In coordinates (m,u,w,z), these are the complete intersections
u²=15m²+1210z² or u²=10m²+1215z², together with w²=4m²+45z².
The Hessian-pencil discriminants are nonzero. Cremona–Fisher–Stoll Theorem 2.8(ii) therefore gives
smoothness, properness,
geometric integrality, canonical H0=Q and structure-sheaf H1dimension1.
Both schemes have the rational point (1:35:7:1).
-/
namespace Z2Z4Rank6.ThirdTwistPairGeometry
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def leading (ε : Bool) : ℚ := if ε then 10 else 15
def constant (ε : Bool) : ℚ := if ε then 1215 else 1210

def radicand (ε : Bool) : Fin 2 → Polynomial ℚ :=
  ![if ε then FunctionField.secondPolynomial else FunctionField.firstPolynomial,
    ThirdTwistField.thirdPolynomial]

def model (ε : Bool) : QuadricIntersectionModel.Model where
  polynomial := ![MvPolynomial.X 1^2-C (leading ε)*MvPolynomial.X 0^2-
      C (constant ε)*MvPolynomial.X 3^2,
    MvPolynomial.X 2^2-C (4:ℚ)*MvPolynomial.X 0^2-C (45:ℚ)*MvPolynomial.X 3^2]
  homogeneous := by
    intro i
    fin_cases i
    · exact (((isHomogeneous_X ℚ (1:Fin 4)).pow 2).sub
        (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul (leading ε))).sub
        (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul (constant ε))
    · exact (((isHomogeneous_X ℚ (2:Fin 4)).pow 2).sub
        (((isHomogeneous_X ℚ (0:Fin 4)).pow 2).C_mul 4)).sub
        (((isHomogeneous_X ℚ (3:Fin 4)).pow 2).C_mul 45)

abbrev PolynomialRing := QuadricIntersectionModel.PolynomialRing
abbrev relation (ε : Bool) := (model ε).polynomial
abbrev definingIdeal (ε : Bool) := QuadricIntersectionModel.definingIdeal (model ε)
abbrev CoordinateRing (ε : Bool) := QuadricIntersectionModel.CoordinateRing (model ε)
abbrev grading (ε : Bool) := QuadricIntersectionModel.grading (model ε)
abbrev scheme (ε : Bool) := QuadricIntersectionModel.scheme (model ε)
abbrev structureMap (ε : Bool) := QuadricIntersectionModel.structureMap (model ε)

def coordinate (ε : Bool) (i : Fin 4) : CoordinateRing ε :=
  Ideal.Quotient.mk (definingIdeal ε) (MvPolynomial.X i)
abbrev m (ε : Bool) := coordinate ε 0
abbrev u (ε : Bool) := coordinate ε 1
abbrev w (ε : Bool) := coordinate ε 2
abbrev z (ε : Bool) := coordinate ε 3

theorem coordinate_degree (ε : Bool) (i : Fin 4) : coordinate ε i∈grading ε 1 :=
  ⟨MvPolynomial.X i,isHomogeneous_X ℚ i,rfl⟩

theorem coordinate_relation (ε : Bool) (i : Fin 2) :
    Ideal.Quotient.mk (definingIdeal ε) (relation ε i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem u_sq (ε : Bool) : (u ε)^2=algebraMap ℚ (CoordinateRing ε) (leading ε)*(m ε)^2+
    algebraMap ℚ (CoordinateRing ε) (constant ε)*(z ε)^2 := by
  have h := coordinate_relation ε 0
  change Ideal.Quotient.mk (definingIdeal ε)
    (MvPolynomial.X 1^2-C (leading ε)*MvPolynomial.X 0^2-C (constant ε)*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change (u ε)^2-algebraMap ℚ (CoordinateRing ε) (leading ε)*(m ε)^2-
    algebraMap ℚ (CoordinateRing ε) (constant ε)*(z ε)^2=0 at h
  linear_combination h

theorem w_sq (ε : Bool) : (w ε)^2=4*(m ε)^2+45*(z ε)^2 := by
  have h := coordinate_relation ε 1
  change Ideal.Quotient.mk (definingIdeal ε)
    (MvPolynomial.X 2^2-C (4:ℚ)*MvPolynomial.X 0^2-C (45:ℚ)*MvPolynomial.X 3^2)=0 at h
  simp only [map_sub,map_pow,map_mul] at h
  change (w ε)^2-4*(m ε)^2-45*(z ε)^2=0 at h
  linear_combination h

@[simp] private theorem pderiv_two (i : Fin 4) : MvPolynomial.pderiv i (2:PolynomialRing)=0 := by
  rw [show (2:PolynomialRing)=1+1 by ring]
  simp

theorem hessian_zero (ε : Bool) : QuadricIntersectionModel.hessian (model ε) 0=
    Matrix.diagonal ![-2*leading ε,2,0,-2*constant ε] := by
  ext i j
  cases ε <;> fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,leading,constant,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Matrix.diagonal]

theorem hessian_one (ε : Bool) : QuadricIntersectionModel.hessian (model ε) 1=
    Matrix.diagonal ![-8,0,2,-90] := by
  ext i j
  cases ε <;> fin_cases i <;> fin_cases j <;>
    norm_num [QuadricIntersectionModel.hessian,model,leading,constant,MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_X,Matrix.diagonal]

theorem pencilPolynomial_eq (ε : Bool) : QuadricIntersectionModel.pencilPolynomial (model ε)=
    16*Polynomial.X*(Polynomial.C (leading ε)*Polynomial.X+4)*
      (Polynomial.C (constant ε)*Polynomial.X+45) := by
  have hm : (fun i j=>Polynomial.C (QuadricIntersectionModel.hessian (model ε) 0 i j)*Polynomial.X+
      Polynomial.C (QuadricIntersectionModel.hessian (model ε) 1 i j))=
      Matrix.diagonal ![-2*Polynomial.C (leading ε)*Polynomial.X-8,2*Polynomial.X,2,
        -2*Polynomial.C (constant ε)*Polynomial.X-90] := by
    rw [hessian_zero,hessian_one]
    ext i j
    cases ε <;> fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal,leading,constant,Polynomial.C_ofNat,Polynomial.coeff_neg,sub_eq_add_neg]
  rw [QuadricIntersectionModel.pencilPolynomial,hm,Matrix.det_diagonal]
  simp [Fin.prod_univ_succ]
  ring

theorem pencilPolynomial_expanded (ε : Bool) : QuadricIntersectionModel.pencilPolynomial (model ε)=
    Polynomial.C (16*leading ε*constant ε)*Polynomial.X^3+
      Polynomial.C (16*(45*leading ε+4*constant ε))*Polynomial.X^2+
      Polynomial.C 2880*Polynomial.X := by
  rw [pencilPolynomial_eq]
  simp only [map_mul,map_add,map_ofNat]
  ring

theorem discriminant_eq (ε : Bool) : QuadricIntersectionModel.discriminant (model ε)=
    if ε then 6096136399021670400000000 else 12134117918180966400000000 := by
  cases ε <;> norm_num [QuadricIntersectionModel.discriminant,QuadricIntersectionModel.c4,
    QuadricIntersectionModel.c6,QuadricIntersectionModel.invariantI,
    QuadricIntersectionModel.invariantJ,pencilPolynomial_expanded,leading,constant,
    Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,Polynomial.coeff_X]

theorem discriminant_ne_zero (ε : Bool) : QuadricIntersectionModel.discriminant (model ε)≠0 := by
  rw [discriminant_eq]
  cases ε <;> norm_num

/-- Genus one of both complete intersections. -/
theorem genus_one (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    RationalCurveGenus.IsSmoothProperGenusOne (scheme ε) (structureMap ε) :=
  QuadricIntersectionModel.genus_one h (model ε) (discriminant_ne_zero ε)

def printedEvaluation (ε : Bool) : CoordinateRing ε →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![(1:ℚ),35,7,1]) (by
    have hker : definingIdeal ε≤RingHom.ker
        (MvPolynomial.aeval ![(1:ℚ),35,7,1]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![(1:ℚ),35,7,1]) (relation ε i)=0
      cases ε <;> fin_cases i <;> norm_num [relation,model,leading,constant]
    intro p hp
    exact hker hp)

@[simp] theorem printedEvaluation_coordinate (ε : Bool) (i : Fin 4) :
    printedEvaluation ε (coordinate ε i)=![(1:ℚ),35,7,1] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

instance gradeZero_scalarTower (ε : Bool) : IsScalarTower ℚ (grading ε 0) (CoordinateRing ε) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=grading ε 0) (A:=CoordinateRing ε) rfl

/-- Rational point (1:35:7:1) on each complete genus-one base. -/
def printedPoint (ε : Bool) : Spec (CommRingCat.of ℚ) ⟶ scheme ε :=
  ProjValuedPoint.point (grading ε) (printedEvaluation ε) (by decide : 0<1)
    (z ε) (coordinate_degree ε 3) (by simp)

theorem printedPoint_over (ε : Bool) : printedPoint ε≫structureMap ε=𝟙 _ := by
  have h := ProjValuedPoint.point_over (grading ε) (printedEvaluation ε) (by decide : 0<1)
    (z ε) (coordinate_degree ε 3) (by simp)
  change printedPoint ε≫structureMap ε=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) at h
  calc
    _=Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) := h
    _=Spec.map (𝟙 (CommRingCat.of ℚ)) := by
      congr 1
    _=𝟙 _ := Spec.map_id _


end
end Z2Z4Rank6.ThirdTwistPairGeometry
