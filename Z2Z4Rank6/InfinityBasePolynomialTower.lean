module

public import Z2Z4Rank6.QuadraticRingMaps

@[expose] public section

/-! The polynomial quadratic tower for the infinity chart:
u²=1210z²+15 and v²=1215z²+10. -/
namespace Z2Z4Rank6.InfinityBaseNormalForm
noncomputable section
open Polynomial
abbrev Poly := ℚ[X]
def firstRadicand : Poly := 1210*Polynomial.X^2+15
def secondRadicand : Poly := 1215*Polynomial.X^2+10
abbrev First := QuadraticAlgebra Poly firstRadicand 0
def secondRadicandFirst : First := algebraMap Poly First secondRadicand
abbrev Tower := QuadraticAlgebra First secondRadicandFirst 0

def towerM : Tower := algebraMap Poly Tower Polynomial.X
def towerU : Tower := algebraMap First Tower QuadraticAlgebra.omega
def towerV : Tower := QuadraticAlgebra.omega

theorem towerU_sq : towerU^2=1210*towerM^2+15 := by
  rw [towerU,←map_pow,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero,
    ←IsScalarTower.algebraMap_apply Poly First Tower]
  simp only [firstRadicand,map_mul,map_add,map_pow,map_ofNat,towerM]

theorem towerV_sq : towerV^2=1215*towerM^2+10 := by
  have hroot : towerV^2=algebraMap First Tower secondRadicandFirst := by
    rw [towerV,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  calc
    towerV^2=algebraMap First Tower secondRadicandFirst := hroot
    _=algebraMap Poly Tower secondRadicand :=
      (IsScalarTower.algebraMap_apply Poly First Tower secondRadicand).symm
    _=1215*towerM^2+10 := by
      simp only [secondRadicand,map_mul,map_add,map_pow,map_ofNat,towerM]
    
end
end Z2Z4Rank6.InfinityBaseNormalForm
