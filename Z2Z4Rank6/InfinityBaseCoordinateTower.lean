import Z2Z4Rank6.InfinityBasePolynomialTower
import Z2Z4Rank6.ProjectiveBaseSchemeInfinityData
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! Both infinity-chart relations yield the universal maps to and
from its polynomial quadratic tower. The quotient embedding has a checked
left inverse on all three generators. -/
namespace Z2Z4Rank6.InfinityBaseNormalForm
noncomputable section
open Polynomial
abbrev CoordinateRing := ProjectiveBaseSchemeCharts.InfinityCoordinateRing

def coordinateToTower : CoordinateRing→ₐ[ℚ]Tower :=
  Ideal.Quotient.liftₐ ProjectiveBaseSchemeCharts.infinityIdeal
    (MvPolynomial.aeval ![towerM,towerU,towerV]) (by
      have hker : ProjectiveBaseSchemeCharts.infinityIdeal≤RingHom.ker
          (MvPolynomial.aeval ![towerM,towerU,towerV]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval ![towerM,towerU,towerV]) (ProjectiveBaseSchemeCharts.infinityRelation i)=0
        fin_cases i <;> simp [ProjectiveBaseSchemeCharts.infinityRelation,towerU_sq,towerV_sq]
      intro p hp
      exact hker hp)

@[simp] theorem coordinateToTower_m : coordinateToTower ProjectiveBaseSchemeCharts.infinityZ=towerM := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 0)=towerM
  simp
@[simp] theorem coordinateToTower_u : coordinateToTower ProjectiveBaseSchemeCharts.infinityU=towerU := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 1)=towerU
  simp
@[simp] theorem coordinateToTower_v : coordinateToTower ProjectiveBaseSchemeCharts.infinityV=towerV := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 2)=towerV
  simp

def polynomialToCoordinate : Poly→+*CoordinateRing := (aeval ProjectiveBaseSchemeCharts.infinityZ).toRingHom
@[simp] theorem polynomialToCoordinate_X : polynomialToCoordinate Polynomial.X=ProjectiveBaseSchemeCharts.infinityZ := by
  change (aeval ProjectiveBaseSchemeCharts.infinityZ) Polynomial.X=ProjectiveBaseSchemeCharts.infinityZ
  exact aeval_X _

theorem first_coordinate_root : ProjectiveBaseSchemeCharts.infinityU^2=polynomialToCoordinate firstRadicand := by
  simp only [firstRadicand,map_mul,map_add,map_pow,map_ofNat,polynomialToCoordinate_X]
  rw [ProjectiveBaseSchemeCharts.infinity_u_sq]

def firstToCoordinate : First→+*CoordinateRing :=
  quadraticRingLift firstRadicand polynomialToCoordinate ProjectiveBaseSchemeCharts.infinityU first_coordinate_root

theorem second_coordinate_root : ProjectiveBaseSchemeCharts.infinityV^2=firstToCoordinate secondRadicandFirst := by
  rw [secondRadicandFirst,firstToCoordinate,quadraticRingLift_algebraMap]
  simp only [secondRadicand,map_mul,map_add,map_pow,map_ofNat,polynomialToCoordinate_X]
  rw [ProjectiveBaseSchemeCharts.infinity_v_sq]

def towerToCoordinateRing : Tower→+*CoordinateRing :=
  quadraticRingLift secondRadicandFirst firstToCoordinate ProjectiveBaseSchemeCharts.infinityV second_coordinate_root

def towerToCoordinate : Tower→ₐ[ℚ]CoordinateRing where
  __ := towerToCoordinateRing
  commutes' := towerToCoordinateRing.map_rat_algebraMap

@[simp] theorem towerToCoordinate_m : towerToCoordinate towerM=ProjectiveBaseSchemeCharts.infinityZ := by
  change towerToCoordinateRing towerM=_
  rw [towerM,IsScalarTower.algebraMap_apply Poly First Tower]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,firstToCoordinate,
    polynomialToCoordinate_X]
@[simp] theorem towerToCoordinate_u : towerToCoordinate towerU=ProjectiveBaseSchemeCharts.infinityU := by
  change towerToCoordinateRing towerU=_
  rw [towerU]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,firstToCoordinate,
    quadraticRingLift_omega]
@[simp] theorem towerToCoordinate_v : towerToCoordinate towerV=ProjectiveBaseSchemeCharts.infinityV := by
  change towerToCoordinateRing towerV=_
  exact quadraticRingLift_omega _ _ _ _

theorem towerToCoordinate_comp : towerToCoordinate.comp coordinateToTower=AlgHom.id ℚ CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change towerToCoordinate (coordinateToTower ProjectiveBaseSchemeCharts.infinityZ)=ProjectiveBaseSchemeCharts.infinityZ
    rw [coordinateToTower_m,towerToCoordinate_m]
  · change towerToCoordinate (coordinateToTower ProjectiveBaseSchemeCharts.infinityU)=ProjectiveBaseSchemeCharts.infinityU
    rw [coordinateToTower_u,towerToCoordinate_u]
  · change towerToCoordinate (coordinateToTower ProjectiveBaseSchemeCharts.infinityV)=ProjectiveBaseSchemeCharts.infinityV
    rw [coordinateToTower_v,towerToCoordinate_v]

theorem coordinateToTower_injective : Function.Injective coordinateToTower := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate)
  intro z
  exact AlgHom.congr_fun towerToCoordinate_comp z

end
end Z2Z4Rank6.InfinityBaseNormalForm
