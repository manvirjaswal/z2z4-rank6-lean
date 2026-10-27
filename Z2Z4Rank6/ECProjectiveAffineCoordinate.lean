module

public import Z2Z4Rank6.ECProjectiveSchemeAffine
public import Z2Z4Rank6.ECFunctionField
public import Z2Z4Rank6.QuadraticRingMaps
public import Mathlib.Algebra.Ring.Hom.InjSurj

@[expose] public section

/-! The printed EC affine quotient embeds into its polynomial
quadratic normal form and the explicit EC field. Source: Jaswal, Theorem 1.2(a), DOI
10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ECProjectiveAffineFunctionField
noncomputable section
open Polynomial
abbrev Poly := ℚ[X]
abbrev CoordinateRing := ECProjectiveSchemeAffine.CoordinateRing
abbrev Tower := QuadraticAlgebra Poly ECFunctionField.cubicPolynomial 0

def towerX : Tower := algebraMap Poly Tower Polynomial.X
def towerY : Tower := QuadraticAlgebra.omega

theorem tower_equation : towerY^2=towerX^3+towerX^2-137620*towerX-10504000 := by
  have hroot : towerY^2=algebraMap Poly Tower ECFunctionField.cubicPolynomial := by
    rw [towerY,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [hroot]
  simp only [ECFunctionField.cubicPolynomial,map_add,map_sub,map_pow,map_mul,map_ofNat,towerX]

def towerToField : Tower→+*ECFunctionField.K :=
  quadraticCoefficientMap ECFunctionField.cubicPolynomial ECFunctionField.d
    (algebraMap Poly ECFunctionField.Base) ECFunctionField.cubicPolynomial_image

theorem towerToField_injective : Function.Injective towerToField :=
  quadraticCoefficientMap_injective _ _ _ _ (RatFunc.algebraMap_injective ℚ)

@[simp] theorem towerToField_x : towerToField towerX=ECFunctionField.x := by
  rw [towerX,towerToField,quadraticCoefficientMap_algebraMap,RatFunc.algebraMap_X]
  rfl
@[simp] theorem towerToField_y : towerToField towerY=ECFunctionField.y :=
  quadraticCoefficientMap_omega _ _ _ _

def coordinateToTower : CoordinateRing→ₐ[ℚ]Tower :=
  Ideal.Quotient.liftₐ ECProjectiveSchemeAffine.definingIdeal
    (MvPolynomial.aeval ![towerX,towerY]) (by
      have hker : ECProjectiveSchemeAffine.definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![towerX,towerY]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        have hi : i=0 := Subsingleton.elim _ _
        subst i
        change (MvPolynomial.aeval ![towerX,towerY]) (ECProjectiveSchemeAffine.relation 0)=0
        simp only [ECProjectiveSchemeAffine.relation,map_add,map_sub,map_pow,map_mul,map_ofNat,
          MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
        rw [tower_equation]
        ring
      intro p hp
      exact hker hp)

@[simp] theorem coordinateToTower_x : coordinateToTower ECProjectiveSchemeAffine.x=towerX := by
  change (MvPolynomial.aeval ![towerX,towerY]) (MvPolynomial.X 0)=towerX
  simp
@[simp] theorem coordinateToTower_y : coordinateToTower ECProjectiveSchemeAffine.y=towerY := by
  change (MvPolynomial.aeval ![towerX,towerY]) (MvPolynomial.X 1)=towerY
  simp

def polynomialToCoordinate : Poly→+*CoordinateRing := (aeval ECProjectiveSchemeAffine.x).toRingHom
@[simp] theorem polynomialToCoordinate_X : polynomialToCoordinate Polynomial.X=ECProjectiveSchemeAffine.x := by
  change (aeval ECProjectiveSchemeAffine.x) Polynomial.X=ECProjectiveSchemeAffine.x
  exact aeval_X _

theorem coordinate_root : ECProjectiveSchemeAffine.y^2=
    polynomialToCoordinate ECFunctionField.cubicPolynomial := by
  simp only [ECFunctionField.cubicPolynomial,map_add,map_sub,map_pow,map_mul,map_ofNat,polynomialToCoordinate_X]
  exact ECProjectiveSchemeAffine.equation

def towerToCoordinateRing : Tower→+*CoordinateRing :=
  quadraticRingLift ECFunctionField.cubicPolynomial polynomialToCoordinate
    ECProjectiveSchemeAffine.y coordinate_root

def towerToCoordinate : Tower→ₐ[ℚ]CoordinateRing where
  __ := towerToCoordinateRing
  commutes' := towerToCoordinateRing.map_rat_algebraMap

@[simp] theorem towerToCoordinate_x : towerToCoordinate towerX=ECProjectiveSchemeAffine.x := by
  change towerToCoordinateRing towerX=_
  rw [towerX,towerToCoordinateRing,quadraticRingLift_algebraMap,polynomialToCoordinate_X]
@[simp] theorem towerToCoordinate_y : towerToCoordinate towerY=ECProjectiveSchemeAffine.y := by
  change towerToCoordinateRing towerY=_
  exact quadraticRingLift_omega ECFunctionField.cubicPolynomial polynomialToCoordinate
    ECProjectiveSchemeAffine.y coordinate_root

theorem towerToCoordinate_comp : towerToCoordinate.comp coordinateToTower=AlgHom.id ℚ CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change towerToCoordinate (coordinateToTower ECProjectiveSchemeAffine.x)=ECProjectiveSchemeAffine.x
    rw [coordinateToTower_x,towerToCoordinate_x]
  · change towerToCoordinate (coordinateToTower ECProjectiveSchemeAffine.y)=ECProjectiveSchemeAffine.y
    rw [coordinateToTower_y,towerToCoordinate_y]

theorem coordinateToTower_injective : Function.Injective coordinateToTower := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate)
  intro z
  exact AlgHom.congr_fun towerToCoordinate_comp z

def towerFieldAlgHom : Tower→ₐ[ℚ]ECFunctionField.K where
  __ := towerToField
  commutes' := towerToField.map_rat_algebraMap

def coordinateMap : CoordinateRing→ₐ[ℚ]ECFunctionField.K := towerFieldAlgHom.comp coordinateToTower

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  towerToField_injective.comp coordinateToTower_injective
@[simp] theorem coordinateMap_x : coordinateMap ECProjectiveSchemeAffine.x=ECFunctionField.x := by
  change towerToField (coordinateToTower ECProjectiveSchemeAffine.x)=_
  rw [coordinateToTower_x,towerToField_x]
@[simp] theorem coordinateMap_y : coordinateMap ECProjectiveSchemeAffine.y=ECFunctionField.y := by
  change towerToField (coordinateToTower ECProjectiveSchemeAffine.y)=_
  rw [coordinateToTower_y,towerToField_y]

instance ecProjectiveAffineCoordinateRingIsDomain : IsDomain CoordinateRing :=
  coordinateMap_injective.isDomain coordinateMap
end
end Z2Z4Rank6.ECProjectiveAffineFunctionField
