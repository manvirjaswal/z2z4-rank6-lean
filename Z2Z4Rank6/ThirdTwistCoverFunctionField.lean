import Z2Z4Rank6.ThirdTwistCoverGenus
import Z2Z4Rank6.ThirdTwistFieldAffine
import Mathlib.AlgebraicGeometry.FunctionField

/-! The generic-point stalk is the fraction field of the
third-twist affine quotient. Geometric integrality comes from the same published theorem as the
genus. -/
namespace Z2Z4Rank6.ThirdTwistCoverFunctionField
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveCharts ThirdTwistCoverProjectiveSections
open ThirdTwistCoverProjectiveRationalPoints ThirdTwistCoverPoints
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem schemeIntegral (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    IsIntegral scheme := by
  let : GeometricallyIntegral structureMap := ThirdTwistCoverGenus.geometrically_integral hGeo
  exact GeometricallyIntegral.isIntegral_of_subsingleton structureMap

section
variable [IsIntegral scheme]

abbrev ActualField := scheme.functionField
abbrev AffineField := FractionRing ThirdTwistCoverAffine.CoordinateRing

local instance zChart_nonempty : Nonempty zOpen :=
  ⟨zChartSchemeIso.inv (affineRationalPointEquiv branchLift sourcePoint)⟩

local instance actualField_isFractionRing : IsFractionRing Γ(scheme,zOpen) (ActualField) :=
  functionField_isFractionRing_of_isAffineOpen scheme zOpen
    ThirdTwistCoverProjectiveH1.zOpen_isAffine

local instance top_nonempty : Nonempty (⊤ : scheme.Opens) :=
  ⟨⟨(Classical.choice (inferInstance : Nonempty zOpen)).val,trivial⟩⟩

def actualCoefficientMap : ℚ→+*ActualField :=
  (scheme.germToFunctionField ⊤).hom.comp (StructureSheafCohomology.qToGlobal scheme structureMap)

local instance actualFieldRationalAlgebra : Algebra ℚ (ActualField) :=
  actualCoefficientMap.toAlgebra

/-- The generic-point stalk of the scheme is the fraction field
of its dense affine chart. -/
def fractionFieldRingEquiv : ActualField≃+*AffineField :=
  IsLocalization.ringEquivOfRingEquiv (ActualField) AffineField zSectionsRingEquiv
    (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv)

@[simp] theorem fractionFieldRingEquiv_germ (a : Γ(scheme,zOpen)) :
    fractionFieldRingEquiv (scheme.germToFunctionField zOpen a)=
      algebraMap ThirdTwistCoverAffine.CoordinateRing AffineField (zSectionsRingEquiv a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S:=ActualField) (Q:=AffineField)
    (j:=zSectionsRingEquiv) (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv) a

/-- The scheme function field is the degree-eight radical field. -/
def functionFieldEquiv : ActualField≃ₐ[ℚ]ThirdTwistField.K :=
  {fractionFieldRingEquiv.trans ThirdTwistFieldAffine.affineFunctionFieldEquiv.toRingEquiv with
    commutes' := (fractionFieldRingEquiv.trans
      ThirdTwistFieldAffine.affineFunctionFieldEquiv.toRingEquiv).toRingHom.map_rat_algebraMap}

@[simp] theorem functionFieldEquiv_germ (a : Γ(scheme,zOpen)) :
    functionFieldEquiv (scheme.germToFunctionField zOpen a)=
      ThirdTwistFieldAffine.coordinateMap (zSectionsRingEquiv a) := by
  change ThirdTwistFieldAffine.affineFunctionFieldEquiv
    (fractionFieldRingEquiv (scheme.germToFunctionField zOpen a))=_
  rw [fractionFieldRingEquiv_germ]
  exact ThirdTwistFieldAffine.fractionMap_algebraMap _

def coordinateM : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm ThirdTwistCoverAffine.m)
def coordinateRoot (i : Fin 3) : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm (TripleSquareCover.root ThirdTwistCoverAffine.radicand i))

@[simp] theorem functionFieldEquiv_m : functionFieldEquiv coordinateM=ThirdTwistField.m := by
  dsimp only [coordinateM]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,ThirdTwistFieldAffine.coordinateMap_m]
@[simp] theorem functionFieldEquiv_root (i : Fin 3) :
    functionFieldEquiv (coordinateRoot i)=![ThirdTwistField.u,ThirdTwistField.v,ThirdTwistField.w] i := by
  dsimp only [coordinateRoot]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,ThirdTwistFieldAffine.coordinateMap_root]
end

/-- The field comparison uses the geometric-integrality hypothesis. -/
def functionFieldEquivOfGeometry (hGeo : SmoothProperGlobalConstantsGeometricIntegralityTheorem) :
    letI : IsIntegral scheme := schemeIntegral hGeo
    letI : Algebra ℚ scheme.functionField := actualFieldRationalAlgebra
    scheme.functionField≃ₐ[ℚ]ThirdTwistField.K := by
  letI : IsIntegral scheme := schemeIntegral hGeo
  exact functionFieldEquiv

end
end Z2Z4Rank6.ThirdTwistCoverFunctionField
