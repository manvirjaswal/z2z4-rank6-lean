import Z2Z4Rank6.AffineBaseFunctionFieldIsoTower
import Z2Z4Rank6.AffineBaseScheme
import Mathlib.Algebra.Ring.Hom.InjSurj

/-! The affine quotient embeds in its polynomial quadratic normal-form
tower, and hence in Q(C). The left inverse is constructed from the quotient
coordinates by the quadratic root universal properties. Domain is a conclusion.
Source: Jaswal (1.3), Theorem 1.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section
open Polynomial
abbrev CoordinateRing := AffineBaseScheme.CoordinateRing

def coordinateToTower : CoordinateRing→ₐ[ℚ]Tower :=
  Ideal.Quotient.liftₐ AffineBaseScheme.definingIdeal
    (MvPolynomial.aeval ![towerM,towerU,towerV]) (by
      have hker : AffineBaseScheme.definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![towerM,towerU,towerV]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval ![towerM,towerU,towerV]) (AffineBaseScheme.relation i)=0
        fin_cases i <;> simp [AffineBaseScheme.relation,towerU_sq,towerV_sq]
      intro p hp
      exact hker hp)

@[simp] theorem coordinateToTower_m : coordinateToTower AffineBaseScheme.m=towerM := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 0)=towerM
  simp
@[simp] theorem coordinateToTower_u : coordinateToTower AffineBaseScheme.u=towerU := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 1)=towerU
  simp
@[simp] theorem coordinateToTower_v : coordinateToTower AffineBaseScheme.v=towerV := by
  change (MvPolynomial.aeval ![towerM,towerU,towerV]) (MvPolynomial.X 2)=towerV
  simp

def polynomialToCoordinate : Poly→+*CoordinateRing := (aeval AffineBaseScheme.m).toRingHom
@[simp] theorem polynomialToCoordinate_X : polynomialToCoordinate Polynomial.X=AffineBaseScheme.m := by
  change (aeval AffineBaseScheme.m) Polynomial.X=AffineBaseScheme.m
  exact aeval_X _

theorem first_coordinate_root : AffineBaseScheme.u^2=polynomialToCoordinate firstRadicand := by
  simp only [firstRadicand,q1,map_mul,map_add,map_pow,map_ofNat,polynomialToCoordinate_X]
  rw [AffineBaseScheme.u_sq]
  ring

def firstToCoordinate : First→+*CoordinateRing :=
  quadraticRingLift firstRadicand polynomialToCoordinate AffineBaseScheme.u first_coordinate_root

theorem second_coordinate_root : AffineBaseScheme.v^2=firstToCoordinate secondRadicandFirst := by
  rw [secondRadicandFirst,firstToCoordinate,quadraticRingLift_algebraMap]
  simp only [secondRadicand,q2,map_mul,map_add,map_pow,map_ofNat,polynomialToCoordinate_X]
  rw [AffineBaseScheme.v_sq]
  ring

def towerToCoordinateRing : Tower→+*CoordinateRing :=
  quadraticRingLift secondRadicandFirst firstToCoordinate AffineBaseScheme.v second_coordinate_root

def towerToCoordinate : Tower→ₐ[ℚ]CoordinateRing where
  __ := towerToCoordinateRing
  commutes' := towerToCoordinateRing.map_rat_algebraMap

@[simp] theorem towerToCoordinate_m : towerToCoordinate towerM=AffineBaseScheme.m := by
  change towerToCoordinateRing towerM=_
  rw [towerM,IsScalarTower.algebraMap_apply Poly First Tower]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,firstToCoordinate,
    polynomialToCoordinate_X]
@[simp] theorem towerToCoordinate_u : towerToCoordinate towerU=AffineBaseScheme.u := by
  change towerToCoordinateRing towerU=_
  rw [towerU]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,firstToCoordinate,
    quadraticRingLift_omega]
@[simp] theorem towerToCoordinate_v : towerToCoordinate towerV=AffineBaseScheme.v := by
  change towerToCoordinateRing towerV=_
  exact quadraticRingLift_omega _ _ _ _

theorem towerToCoordinate_comp : towerToCoordinate.comp coordinateToTower=AlgHom.id ℚ CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change towerToCoordinate (coordinateToTower AffineBaseScheme.m)=AffineBaseScheme.m
    rw [coordinateToTower_m,towerToCoordinate_m]
  · change towerToCoordinate (coordinateToTower AffineBaseScheme.u)=AffineBaseScheme.u
    rw [coordinateToTower_u,towerToCoordinate_u]
  · change towerToCoordinate (coordinateToTower AffineBaseScheme.v)=AffineBaseScheme.v
    rw [coordinateToTower_v,towerToCoordinate_v]

theorem coordinateToTower_injective : Function.Injective coordinateToTower := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate)
  intro z
  exact AlgHom.congr_fun towerToCoordinate_comp z

def towerFieldAlgHom : Tower→ₐ[ℚ]FunctionField.K where
  __ := towerToField
  commutes' := towerToField.map_rat_algebraMap

/-- The affine-coordinate embedding into the existing Q(C). -/
def coordinateMap : CoordinateRing→ₐ[ℚ]FunctionField.K := towerFieldAlgHom.comp coordinateToTower

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  towerToField_injective.comp coordinateToTower_injective

@[simp] theorem coordinateMap_m : coordinateMap AffineBaseScheme.m=FunctionField.m := by
  change towerToField (coordinateToTower AffineBaseScheme.m)=_
  rw [coordinateToTower_m,towerToField_m]
@[simp] theorem coordinateMap_u : coordinateMap AffineBaseScheme.u=FunctionField.u := by
  change towerToField (coordinateToTower AffineBaseScheme.u)=_
  rw [coordinateToTower_u,towerToField_u]
@[simp] theorem coordinateMap_v : coordinateMap AffineBaseScheme.v=FunctionField.v := by
  change towerToField (coordinateToTower AffineBaseScheme.v)=_
  rw [coordinateToTower_v,towerToField_v]

instance affineBaseCoordinateRingIsDomain : IsDomain CoordinateRing :=
  coordinateMap_injective.isDomain coordinateMap
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
