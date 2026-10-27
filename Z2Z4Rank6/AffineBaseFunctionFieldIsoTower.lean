module

public import Z2Z4Rank6.QuadraticRingMaps
public import Z2Z4Rank6.FunctionField

@[expose] public section

/-! The free four-coefficient polynomial quadratic tower underlying the
affine C coordinate ring. Coefficientwise maps embed it into the
already constructed degree-four field Q(C).
Source: Jaswal (1.3), Theorem 1.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section
open Polynomial
abbrev Poly := ℚ[X]
def firstRadicand : Poly := q1 (Polynomial.X^2)
def secondRadicand : Poly := q2 (Polynomial.X^2)
abbrev First := QuadraticAlgebra Poly firstRadicand 0
def secondRadicandFirst : First := algebraMap Poly First secondRadicand
abbrev Tower := QuadraticAlgebra First secondRadicandFirst 0

def towerM : Tower := algebraMap Poly Tower Polynomial.X
def towerU : Tower := algebraMap First Tower QuadraticAlgebra.omega
def towerV : Tower := QuadraticAlgebra.omega

theorem towerU_sq : towerU^2=15*towerM^2+1210 := by
  rw [towerU,←map_pow,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero,
    ←IsScalarTower.algebraMap_apply Poly First Tower]
  simp only [firstRadicand,q1,map_mul,map_add,map_pow,map_ofNat,towerM]
  ring

theorem towerV_sq : towerV^2=10*towerM^2+1215 := by
  have hroot : towerV^2=algebraMap First Tower secondRadicandFirst := by
    rw [towerV,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  calc
    towerV^2=algebraMap First Tower secondRadicandFirst := hroot
    _=algebraMap Poly Tower secondRadicand :=
      (IsScalarTower.algebraMap_apply Poly First Tower secondRadicand).symm
    _=10*towerM^2+1215 := by
      simp only [secondRadicand,q2,map_mul,map_add,map_pow,map_ofNat,towerM]
      ring

theorem firstRadicand_image : algebraMap Poly FunctionField.Base firstRadicand=FunctionField.d1 := by
  simp only [firstRadicand,FunctionField.d1,q1,map_mul,map_add,map_pow,map_ofNat,RatFunc.algebraMap_X]
theorem secondRadicand_image : algebraMap Poly FunctionField.Base secondRadicand=FunctionField.d2 := by
  simp only [secondRadicand,FunctionField.d2,q2,map_mul,map_add,map_pow,map_ofNat,RatFunc.algebraMap_X]

def firstToField : First→+*FunctionField.First :=
  quadraticCoefficientMap firstRadicand FunctionField.d1
    (algebraMap Poly FunctionField.Base) firstRadicand_image

theorem firstToField_injective : Function.Injective firstToField :=
  quadraticCoefficientMap_injective _ _ _ _ (RatFunc.algebraMap_injective ℚ)

theorem secondRadicandFirst_image : firstToField secondRadicandFirst=FunctionField.d2First := by
  rw [secondRadicandFirst,firstToField,quadraticCoefficientMap_algebraMap,secondRadicand_image]
  rfl

def towerToField : Tower→+*FunctionField.K :=
  quadraticCoefficientMap secondRadicandFirst FunctionField.d2First firstToField secondRadicandFirst_image

theorem towerToField_injective : Function.Injective towerToField :=
  quadraticCoefficientMap_injective _ _ _ _ firstToField_injective

@[simp] theorem towerToField_m : towerToField towerM=FunctionField.m := by
  rw [towerM,IsScalarTower.algebraMap_apply Poly First Tower]
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    RatFunc.algebraMap_X,FunctionField.m]
  exact (IsScalarTower.algebraMap_apply FunctionField.Base FunctionField.First FunctionField.K _).symm

@[simp] theorem towerToField_u : towerToField towerU=FunctionField.u := by
  rw [towerU]
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    quadraticCoefficientMap_omega,FunctionField.u]

@[simp] theorem towerToField_v : towerToField towerV=FunctionField.v :=
  quadraticCoefficientMap_omega _ _ _ _
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
