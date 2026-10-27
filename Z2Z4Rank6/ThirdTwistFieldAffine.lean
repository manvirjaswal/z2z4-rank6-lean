import Z2Z4Rank6.ThirdTwistCoverNormalForm
import Z2Z4Rank6.ThirdTwistFieldCoordinates
import Mathlib.RingTheory.Localization.FractionRing

/-! The affine quotient has the triple-square field as its
fraction field. Injectivity is proved coefficient by coefficient in the
three polynomial quadratic normal forms. -/
namespace Z2Z4Rank6.ThirdTwistFieldAffine
noncomputable section
open Polynomial
abbrev f := ThirdTwistCoverAffine.radicand
abbrev Poly := TripleSquareCover.Poly
abbrev First := TripleSquareCover.First f
abbrev Second := TripleSquareCover.Second f
abbrev Tower := TripleSquareCover.Tower f
abbrev CoordinateRing := ThirdTwistCoverAffine.CoordinateRing

private theorem first_image : algebraMap Poly ThirdTwistField.Base (f 0)=FunctionField.d1 := by
  simp [f,ThirdTwistCoverAffine.radicand,ThirdTwistCoverPolynomialData.affineRadicand,
    FunctionField.d1,q1,RatFunc.algebraMap_X,map_ofNat]
  ring

private theorem second_image : algebraMap Poly ThirdTwistField.Base (f 1)=FunctionField.d2 := by
  simp [f,ThirdTwistCoverAffine.radicand,ThirdTwistCoverPolynomialData.affineRadicand,
    FunctionField.d2,q2,RatFunc.algebraMap_X,map_ofNat]
  ring

private theorem third_image : algebraMap Poly ThirdTwistField.Base (f 2)=ThirdTwistField.d3 := by
  simp [f,ThirdTwistCoverAffine.radicand,ThirdTwistCoverPolynomialData.affineRadicand,
    ThirdTwistField.d3,RatFunc.algebraMap_X,map_ofNat]

def firstToField : First →+* FunctionField.First :=
  quadraticCoefficientMap (f 0) FunctionField.d1
    (algebraMap Poly ThirdTwistField.Base) first_image

theorem firstToField_injective : Function.Injective firstToField :=
  quadraticCoefficientMap_injective _ _ _ _ (RatFunc.algebraMap_injective ℚ)

private theorem secondRadicand_image :
    firstToField (TripleSquareCover.secondRadicand f)=FunctionField.d2First := by
  rw [TripleSquareCover.secondRadicand,firstToField,quadraticCoefficientMap_algebraMap,second_image]
  rfl

def secondToField : Second →+* FunctionField.K :=
  quadraticCoefficientMap (TripleSquareCover.secondRadicand f) FunctionField.d2First
    firstToField secondRadicand_image

theorem secondToField_injective : Function.Injective secondToField :=
  quadraticCoefficientMap_injective _ _ _ _ firstToField_injective

theorem secondToField_polynomial (p : Poly) :
    secondToField (algebraMap Poly Second p)=
      algebraMap ThirdTwistField.Base FunctionField.K (algebraMap Poly ThirdTwistField.Base p) := by
  rw [IsScalarTower.algebraMap_apply Poly First Second]
  simp only [secondToField,quadraticCoefficientMap_algebraMap,firstToField]
  exact (IsScalarTower.algebraMap_apply ThirdTwistField.Base FunctionField.First FunctionField.K _).symm

private theorem thirdRadicand_image :
    secondToField (TripleSquareCover.thirdRadicand f)=ThirdTwistField.d3Old := by
  rw [TripleSquareCover.thirdRadicand,secondToField_polynomial,third_image]
  rfl

def towerToField : Tower →+* ThirdTwistField.K :=
  quadraticCoefficientMap (TripleSquareCover.thirdRadicand f) ThirdTwistField.d3Old
    secondToField thirdRadicand_image

theorem towerToField_injective : Function.Injective towerToField :=
  quadraticCoefficientMap_injective _ _ _ _ secondToField_injective

@[simp] theorem towerToField_parameter :
    towerToField (TripleSquareCover.towerParameter f)=ThirdTwistField.m := by
  rw [TripleSquareCover.towerParameter,IsScalarTower.algebraMap_apply Poly Second Tower]
  simp only [towerToField,quadraticCoefficientMap_algebraMap,secondToField_polynomial,RatFunc.algebraMap_X]
  rfl

@[simp] theorem towerToField_root (i : Fin 3) :
    towerToField (TripleSquareCover.towerRoot f i)=
      ![ThirdTwistField.u,ThirdTwistField.v,ThirdTwistField.w] i := by
  fin_cases i
  · change towerToField (TripleSquareCover.towerRoot f 0)=ThirdTwistField.u
    rw [TripleSquareCover.towerRoot_zero,
      IsScalarTower.algebraMap_apply First Second Tower]
    simp only [towerToField,quadraticCoefficientMap_algebraMap,secondToField,
      firstToField,quadraticCoefficientMap_omega]
    rfl
  · change towerToField (TripleSquareCover.towerRoot f 1)=ThirdTwistField.v
    rw [TripleSquareCover.towerRoot_one]
    simp only [towerToField,quadraticCoefficientMap_algebraMap,secondToField,quadraticCoefficientMap_omega]
    rfl
  · change towerToField (TripleSquareCover.towerRoot f 2)=ThirdTwistField.w
    rw [TripleSquareCover.towerRoot_two]
    exact quadraticCoefficientMap_omega _ _ _ _

def towerFieldAlgHom : Tower →ₐ[ℚ] ThirdTwistField.K where
  __ := towerToField
  commutes' := towerToField.map_rat_algebraMap

def coordinateMap : CoordinateRing →ₐ[ℚ] ThirdTwistField.K :=
  towerFieldAlgHom.comp (TripleSquareCover.coordinateToTower f)

theorem coordinateMap_injective : Function.Injective coordinateMap :=
  towerToField_injective.comp (TripleSquareCover.coordinateToTower_injective f)

@[simp] theorem coordinateMap_m : coordinateMap ThirdTwistCoverAffine.m=ThirdTwistField.m := by
  change towerToField (TripleSquareCover.coordinateToTower f (TripleSquareCover.parameter f))=_
  rw [TripleSquareCover.coordinateToTower_parameter,towerToField_parameter]

@[simp] theorem coordinateMap_root (i : Fin 3) :
    coordinateMap (TripleSquareCover.root f i)=
      ![ThirdTwistField.u,ThirdTwistField.v,ThirdTwistField.w] i := by
  change towerToField (TripleSquareCover.coordinateToTower f (TripleSquareCover.root f i))=_
  rw [TripleSquareCover.coordinateToTower_root,towerToField_root]

instance coordinateRingIsDomain : IsDomain CoordinateRing :=
  coordinateMap_injective.isDomain coordinateMap

abbrev AffineField := FractionRing CoordinateRing

def fractionMapRing : AffineField →+* ThirdTwistField.K :=
  IsFractionRing.lift coordinateMap_injective

def fractionMap : AffineField →ₐ[ℚ] ThirdTwistField.K where
  __ := fractionMapRing
  commutes' := fractionMapRing.map_rat_algebraMap

@[simp] theorem fractionMap_algebraMap (z : CoordinateRing) :
    fractionMap (algebraMap CoordinateRing AffineField z)=coordinateMap z :=
  IsFractionRing.lift_algebraMap coordinateMap_injective z

@[simp] theorem fractionMap_m :
    fractionMap (algebraMap CoordinateRing AffineField ThirdTwistCoverAffine.m)=ThirdTwistField.m := by
  rw [fractionMap_algebraMap,coordinateMap_m]

@[simp] theorem fractionMap_root (i : Fin 3) :
    fractionMap (algebraMap CoordinateRing AffineField (TripleSquareCover.root f i))=
      ![ThirdTwistField.u,ThirdTwistField.v,ThirdTwistField.w] i := by
  rw [fractionMap_algebraMap,coordinateMap_root]

theorem fractionMap_surjective : Function.Surjective fractionMap := by
  have hm : ThirdTwistField.m∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ThirdTwistCoverAffine.m,fractionMap_m⟩
  have hu : ThirdTwistField.u∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ThirdTwistCoverAffine.u,fractionMap_root 0⟩
  have hv : ThirdTwistField.v∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ThirdTwistCoverAffine.v,fractionMap_root 1⟩
  have hw : ThirdTwistField.w∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ThirdTwistCoverAffine.w,fractionMap_root 2⟩
  have hle : IntermediateField.adjoin ℚ
      ({ThirdTwistField.m,ThirdTwistField.u,ThirdTwistField.v,ThirdTwistField.w}:Set ThirdTwistField.K)
        ≤fractionMap.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl|rfl
    · exact hm
    · exact hu
    · exact hv
    · exact hw
  rw [ThirdTwistField.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

def affineFunctionFieldEquiv : FractionRing CoordinateRing ≃ₐ[ℚ] ThirdTwistField.K :=
  AlgEquiv.ofBijective fractionMap ⟨fractionMap.injective,fractionMap_surjective⟩

end
end Z2Z4Rank6.ThirdTwistFieldAffine
