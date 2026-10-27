module

public import Z2Z4Rank6.ThirdTwistPairGeometry
public import Z2Z4Rank6.GTorsionCoverDoubleNormalForm
public import Z2Z4Rank6.ThirdTwistFieldCoordinates
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! The affine quotients and their fraction fields, with the qi root
first and the third-twist root second. Injectivity follows from the
four-coefficient polynomial quadratic normal form. Surjectivity follows
from the proved field generators. -/
namespace Z2Z4Rank6.ThirdTwistPairGeometry
noncomputable section
open Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Affine
abbrev CoordinateRing (ε : Bool) := DoubleSquareCover.CoordinateRing (radicand ε)
abbrev m (ε : Bool) := DoubleSquareCover.parameter (radicand ε)
abbrev u (ε : Bool) := DoubleSquareCover.root (radicand ε) 0
abbrev w (ε : Bool) := DoubleSquareCover.root (radicand ε) 1

theorem u_sq (ε : Bool) : (u ε)^2=
    algebraMap ℚ (CoordinateRing ε) (leading ε)*(m ε)^2+
      algebraMap ℚ (CoordinateRing ε) (constant ε) := by
  have h := DoubleSquareCover.root_sq (radicand ε) 0
  cases ε <;> norm_num [radicand,FunctionField.firstPolynomial,FunctionField.secondPolynomial,
    leading,constant,DoubleSquareCover.parameter] at h ⊢
  all_goals norm_num only [map_ofNat] at h ⊢
  all_goals linear_combination h

theorem w_sq (ε : Bool) : (w ε)^2=4*(m ε)^2+45 := by
  have h := DoubleSquareCover.root_sq (radicand ε) 1
  change (w ε)^2=Polynomial.aeval (m ε) (4*Polynomial.X^2+45) at h
  simpa only [map_add,map_mul,map_pow,map_ofNat,Polynomial.aeval_X] using h

namespace PairOne
abbrev First := DoubleSquareCover.First (radicand false)
abbrev Tower := DoubleSquareCover.Tower (radicand false)
abbrev K := ThirdTwistField.PairOne

theorem firstRadicand_image : algebraMap (Polynomial ℚ) ThirdTwistField.Base (radicand false 0)=
    FunctionField.d1 := ThirdTwistField.firstPolynomial_image

def firstToField : First →+* FunctionField.First :=
  quadraticCoefficientMap _ FunctionField.d1
    (algebraMap (Polynomial ℚ) ThirdTwistField.Base) firstRadicand_image

theorem firstToField_injective : Function.Injective firstToField :=
  quadraticCoefficientMap_injective _ _ _ _ (RatFunc.algebraMap_injective ℚ)

theorem secondRadicand_image :
    firstToField (DoubleSquareCover.secondRadicand (radicand false))=ThirdTwistField.d3First := by
  rw [DoubleSquareCover.secondRadicand,firstToField,quadraticCoefficientMap_algebraMap]
  change algebraMap ThirdTwistField.Base FunctionField.First
    (algebraMap (Polynomial ℚ) ThirdTwistField.Base ThirdTwistField.thirdPolynomial)=_
  rw [ThirdTwistField.thirdPolynomial_image]
  rfl

def towerToField : Tower →+* K :=
  quadraticCoefficientMap _ ThirdTwistField.d3First firstToField secondRadicand_image

theorem towerToField_injective : Function.Injective towerToField :=
  quadraticCoefficientMap_injective _ _ _ _ firstToField_injective

@[simp] theorem towerToField_m :
    towerToField (DoubleSquareCover.towerParameter (radicand false))=ThirdTwistField.PairOne.m := by
  change towerToField (algebraMap (Polynomial ℚ) Tower Polynomial.X)=_
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) First Tower]
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    RatFunc.algebraMap_X,ThirdTwistField.PairOne.m]
  exact (IsScalarTower.algebraMap_apply ThirdTwistField.Base FunctionField.First K _).symm

@[simp] theorem towerToField_u :
    towerToField (DoubleSquareCover.towerRoot (radicand false) 0)=ThirdTwistField.PairOne.u := by
  change towerToField (algebraMap First Tower QuadraticAlgebra.omega)=_
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    quadraticCoefficientMap_omega,ThirdTwistField.PairOne.u]

@[simp] theorem towerToField_w :
    towerToField (DoubleSquareCover.towerRoot (radicand false) 1)=ThirdTwistField.PairOne.w :=
  quadraticCoefficientMap_omega _ _ _ _

def coordinateMap : CoordinateRing false →ₐ[ℚ] K :=
  towerToField.toRatAlgHom.comp (DoubleSquareCover.coordinateTowerEquiv (radicand false)).toAlgHom

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  towerToField_injective.comp (DoubleSquareCover.coordinateTowerEquiv (radicand false)).injective

@[simp] theorem coordinateMap_m : coordinateMap (m false)=ThirdTwistField.PairOne.m := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.parameter _))=_
  rw [DoubleSquareCover.coordinateToTower_parameter,towerToField_m]
@[simp] theorem coordinateMap_u : coordinateMap (u false)=ThirdTwistField.PairOne.u := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.root _ 0))=_
  rw [DoubleSquareCover.coordinateToTower_root,towerToField_u]
@[simp] theorem coordinateMap_w : coordinateMap (w false)=ThirdTwistField.PairOne.w := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.root _ 1))=_
  rw [DoubleSquareCover.coordinateToTower_root,towerToField_w]

instance coordinateRing_domain : IsDomain (CoordinateRing false) :=
  coordinateMap_injective.isDomain coordinateMap

abbrev AffineField := FractionRing (CoordinateRing false)
def fractionMap : AffineField →ₐ[ℚ] K :=
  (IsFractionRing.lift coordinateMap_injective).toRatAlgHom

@[simp] theorem fractionMap_algebraMap (a : CoordinateRing false) :
    fractionMap (algebraMap (CoordinateRing false) AffineField a)=coordinateMap a :=
  IsFractionRing.lift_algebraMap coordinateMap_injective a

theorem fractionMap_surjective : Function.Surjective fractionMap := by
  have hm : ThirdTwistField.PairOne.m∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing false) AffineField (m false),by simp⟩
  have hu : ThirdTwistField.PairOne.u∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing false) AffineField (u false),by simp⟩
  have hw : ThirdTwistField.PairOne.w∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing false) AffineField (w false),by simp⟩
  have hle : IntermediateField.adjoin ℚ
      ({ThirdTwistField.PairOne.m,ThirdTwistField.PairOne.u,ThirdTwistField.PairOne.w} : Set K)
        ≤fractionMap.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl
    · exact hm
    · exact hu
    · exact hw
  rw [ThirdTwistField.PairOne.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- Affine fraction field identified with the rank computation's first pair field. -/
def affineFunctionFieldEquiv : AffineField ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective fractionMap ⟨fractionMap.injective,fractionMap_surjective⟩
end PairOne

namespace PairTwo
abbrev First := DoubleSquareCover.First (radicand true)
abbrev Tower := DoubleSquareCover.Tower (radicand true)
abbrev K := ThirdTwistField.PairTwo

theorem firstRadicand_image : algebraMap (Polynomial ℚ) ThirdTwistField.Base (radicand true 0)=
    FunctionField.d2 := ThirdTwistField.secondPolynomial_image

def firstToField : First →+* ThirdTwistField.PairTwoFirst :=
  quadraticCoefficientMap _ FunctionField.d2
    (algebraMap (Polynomial ℚ) ThirdTwistField.Base) firstRadicand_image

theorem firstToField_injective : Function.Injective firstToField :=
  quadraticCoefficientMap_injective _ _ _ _ (RatFunc.algebraMap_injective ℚ)

theorem secondRadicand_image :
    firstToField (DoubleSquareCover.secondRadicand (radicand true))=ThirdTwistField.d3PairTwoFirst := by
  rw [DoubleSquareCover.secondRadicand,firstToField,quadraticCoefficientMap_algebraMap]
  change algebraMap ThirdTwistField.Base ThirdTwistField.PairTwoFirst
    (algebraMap (Polynomial ℚ) ThirdTwistField.Base ThirdTwistField.thirdPolynomial)=_
  rw [ThirdTwistField.thirdPolynomial_image]
  rfl

def towerToField : Tower →+* K :=
  quadraticCoefficientMap _ ThirdTwistField.d3PairTwoFirst firstToField secondRadicand_image

theorem towerToField_injective : Function.Injective towerToField :=
  quadraticCoefficientMap_injective _ _ _ _ firstToField_injective

@[simp] theorem towerToField_m :
    towerToField (DoubleSquareCover.towerParameter (radicand true))=ThirdTwistField.PairTwo.m := by
  change towerToField (algebraMap (Polynomial ℚ) Tower Polynomial.X)=_
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) First Tower]
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    RatFunc.algebraMap_X,ThirdTwistField.PairTwo.m]
  exact (IsScalarTower.algebraMap_apply ThirdTwistField.Base ThirdTwistField.PairTwoFirst K _).symm

@[simp] theorem towerToField_u :
    towerToField (DoubleSquareCover.towerRoot (radicand true) 0)=ThirdTwistField.PairTwo.u := by
  change towerToField (algebraMap First Tower QuadraticAlgebra.omega)=_
  simp only [towerToField,quadraticCoefficientMap_algebraMap,firstToField,
    quadraticCoefficientMap_omega,ThirdTwistField.PairTwo.u]

@[simp] theorem towerToField_w :
    towerToField (DoubleSquareCover.towerRoot (radicand true) 1)=ThirdTwistField.PairTwo.w :=
  quadraticCoefficientMap_omega _ _ _ _

def coordinateMap : CoordinateRing true →ₐ[ℚ] K :=
  towerToField.toRatAlgHom.comp (DoubleSquareCover.coordinateTowerEquiv (radicand true)).toAlgHom

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  towerToField_injective.comp (DoubleSquareCover.coordinateTowerEquiv (radicand true)).injective

@[simp] theorem coordinateMap_m : coordinateMap (m true)=ThirdTwistField.PairTwo.m := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.parameter _))=_
  rw [DoubleSquareCover.coordinateToTower_parameter,towerToField_m]
@[simp] theorem coordinateMap_u : coordinateMap (u true)=ThirdTwistField.PairTwo.u := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.root _ 0))=_
  rw [DoubleSquareCover.coordinateToTower_root,towerToField_u]
@[simp] theorem coordinateMap_w : coordinateMap (w true)=ThirdTwistField.PairTwo.w := by
  change towerToField (DoubleSquareCover.coordinateToTower _ (DoubleSquareCover.root _ 1))=_
  rw [DoubleSquareCover.coordinateToTower_root,towerToField_w]

instance coordinateRing_domain : IsDomain (CoordinateRing true) :=
  coordinateMap_injective.isDomain coordinateMap

abbrev AffineField := FractionRing (CoordinateRing true)
def fractionMap : AffineField →ₐ[ℚ] K :=
  (IsFractionRing.lift coordinateMap_injective).toRatAlgHom

@[simp] theorem fractionMap_algebraMap (a : CoordinateRing true) :
    fractionMap (algebraMap (CoordinateRing true) AffineField a)=coordinateMap a :=
  IsFractionRing.lift_algebraMap coordinateMap_injective a

theorem fractionMap_surjective : Function.Surjective fractionMap := by
  have hm : ThirdTwistField.PairTwo.m∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing true) AffineField (m true),by simp⟩
  have hu : ThirdTwistField.PairTwo.u∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing true) AffineField (u true),by simp⟩
  have hw : ThirdTwistField.PairTwo.w∈fractionMap.fieldRange :=
    ⟨algebraMap (CoordinateRing true) AffineField (w true),by simp⟩
  have hle : IntermediateField.adjoin ℚ
      ({ThirdTwistField.PairTwo.m,ThirdTwistField.PairTwo.u,ThirdTwistField.PairTwo.w} : Set K)
        ≤fractionMap.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl
    · exact hm
    · exact hu
    · exact hw
  rw [ThirdTwistField.PairTwo.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

def affineFunctionFieldEquiv : AffineField ≃ₐ[ℚ] K :=
  AlgEquiv.ofBijective fractionMap ⟨fractionMap.injective,fractionMap_surjective⟩
end PairTwo

end Affine
end
end Z2Z4Rank6.ThirdTwistPairGeometry
