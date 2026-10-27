import Z2Z4Rank6.ThirdTwistPairGeometryCharts
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The projective generic-stalk fields of the two pair bases

The nonempty affine z-chart identifies each projective
function field with the fraction field of its affine coordinate ring.
The previously proved fraction-field equivalences therefore identify these
fields with the exact PairOne/PairTwo fields used for rank computations.
The parameter is the germ of the homogeneous coordinate ratio m/z.
-/
namespace Z2Z4Rank6.ThirdTwistPairGeometry
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FunctionField

theorem scheme_integral (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    IsIntegral (scheme ε) := by
  let : GeometricallyIntegral (structureMap ε) := (genus_one h ε).geometricallyIntegral
  exact GeometricallyIntegral.isIntegral_of_subsingleton (structureMap ε)

instance affineDomain (ε : Bool) : IsDomain (Affine.CoordinateRing ε) := by
  cases ε
  · exact Affine.PairOne.coordinateRing_domain
  · exact Affine.PairTwo.coordinateRing_domain

/-- Mathlib's generic-point stalk of the projective scheme. -/
def ActualField (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) : Type :=
  letI := scheme_integral h ε
  (scheme ε).functionField

instance actualField_field (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    Field (ActualField h ε) := by
  letI := scheme_integral h ε
  change Field (scheme ε).functionField
  infer_instance

instance actualSectionAlgebra (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    Algebra ↥Γ((scheme ε),(Charts.zOpen ε)) (ActualField h ε) := by
  letI := scheme_integral h ε
  change Algebra ↥Γ((scheme ε),(Charts.zOpen ε)) (scheme ε).functionField
  infer_instance

instance actualField_isFractionRing (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    IsFractionRing ↥Γ((scheme ε),(Charts.zOpen ε)) (ActualField h ε) := by
  let := scheme_integral h ε
  change IsFractionRing ↥Γ((scheme ε),(Charts.zOpen ε)) (scheme ε).functionField
  exact functionField_isFractionRing_of_isAffineOpen (scheme ε) (Charts.zOpen ε)
    (Charts.zChart_affine ε)

def fractionFieldRingEquiv (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    ActualField h ε ≃+* FractionRing (Affine.CoordinateRing ε) :=
  IsLocalization.ringEquivOfRingEquiv (ActualField h ε) (FractionRing (Affine.CoordinateRing ε))
    (Charts.zSectionsRingEquiv ε) (MulEquivClass.map_nonZeroDivisors (Charts.zSectionsRingEquiv ε))

instance actualField_charZero (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) :
    CharZero (ActualField h ε) := by
  cases ε
  · exact ((fractionFieldRingEquiv h false).trans
      Affine.PairOne.affineFunctionFieldEquiv.toRingEquiv).toRingHom.charZero
  · exact ((fractionFieldRingEquiv h true).trans
      Affine.PairTwo.affineFunctionFieldEquiv.toRingEquiv).toRingHom.charZero

def germ (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool)
    (a : Γ((scheme ε),(Charts.zOpen ε))) : ActualField h ε := by
  letI := scheme_integral h ε
  exact (scheme ε).germToFunctionField (Charts.zOpen ε) a

theorem fractionFieldRingEquiv_germ (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool)
    (a : Γ((scheme ε),(Charts.zOpen ε))) :
    fractionFieldRingEquiv h ε (germ h ε a)=
      algebraMap (Affine.CoordinateRing ε) (FractionRing (Affine.CoordinateRing ε))
        (Charts.zSectionsRingEquiv ε a) := by
  let := scheme_integral h ε
  exact IsLocalization.ringEquivOfRingEquiv_eq (S:=ActualField h ε)
    (Q:=FractionRing (Affine.CoordinateRing ε)) (j:=Charts.zSectionsRingEquiv ε)
      (MulEquivClass.map_nonZeroDivisors (Charts.zSectionsRingEquiv ε)) a

def coordinateM (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) : ActualField h ε :=
  germ h ε ((Charts.zSectionsRingEquiv ε).symm (Affine.m ε))
def coordinateU (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) : ActualField h ε :=
  germ h ε ((Charts.zSectionsRingEquiv ε).symm (Affine.u ε))
def coordinateW (h : QuadricIntersectionModel.CFSTheorem28ii) (ε : Bool) : ActualField h ε :=
  germ h ε ((Charts.zSectionsRingEquiv ε).symm (Affine.w ε))

/-- Projective generic-stalk field of the q1/q3 pair, with no field cut. -/
def pairOneEquiv (h : QuadricIntersectionModel.CFSTheorem28ii) :
    ActualField h false ≃ₐ[ℚ] ThirdTwistField.PairOne :=
  {(fractionFieldRingEquiv h false).trans Affine.PairOne.affineFunctionFieldEquiv.toRingEquiv with
    commutes' := ((fractionFieldRingEquiv h false).trans
      Affine.PairOne.affineFunctionFieldEquiv.toRingEquiv).toRingHom.map_rat_algebraMap}

/-- Projective generic-stalk field of the q2/q3 pair, with no field cut. -/
def pairTwoEquiv (h : QuadricIntersectionModel.CFSTheorem28ii) :
    ActualField h true ≃ₐ[ℚ] ThirdTwistField.PairTwo :=
  {(fractionFieldRingEquiv h true).trans Affine.PairTwo.affineFunctionFieldEquiv.toRingEquiv with
    commutes' := ((fractionFieldRingEquiv h true).trans
      Affine.PairTwo.affineFunctionFieldEquiv.toRingEquiv).toRingHom.map_rat_algebraMap}

@[simp] theorem pairOneEquiv_m (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairOneEquiv h (coordinateM h false)=ThirdTwistField.PairOne.m := by
  change Affine.PairOne.fractionMap (fractionFieldRingEquiv h false
    (germ h false ((Charts.zSectionsRingEquiv false).symm (Affine.m false))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairOne.fractionMap_algebraMap,Affine.PairOne.coordinateMap_m]

@[simp] theorem pairOneEquiv_u (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairOneEquiv h (coordinateU h false)=ThirdTwistField.PairOne.u := by
  change Affine.PairOne.fractionMap (fractionFieldRingEquiv h false
    (germ h false ((Charts.zSectionsRingEquiv false).symm (Affine.u false))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairOne.fractionMap_algebraMap,Affine.PairOne.coordinateMap_u]

@[simp] theorem pairOneEquiv_w (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairOneEquiv h (coordinateW h false)=ThirdTwistField.PairOne.w := by
  change Affine.PairOne.fractionMap (fractionFieldRingEquiv h false
    (germ h false ((Charts.zSectionsRingEquiv false).symm (Affine.w false))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairOne.fractionMap_algebraMap,Affine.PairOne.coordinateMap_w]

@[simp] theorem pairTwoEquiv_m (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairTwoEquiv h (coordinateM h true)=ThirdTwistField.PairTwo.m := by
  change Affine.PairTwo.fractionMap (fractionFieldRingEquiv h true
    (germ h true ((Charts.zSectionsRingEquiv true).symm (Affine.m true))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairTwo.fractionMap_algebraMap,Affine.PairTwo.coordinateMap_m]

@[simp] theorem pairTwoEquiv_u (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairTwoEquiv h (coordinateU h true)=ThirdTwistField.PairTwo.u := by
  change Affine.PairTwo.fractionMap (fractionFieldRingEquiv h true
    (germ h true ((Charts.zSectionsRingEquiv true).symm (Affine.u true))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairTwo.fractionMap_algebraMap,Affine.PairTwo.coordinateMap_u]

@[simp] theorem pairTwoEquiv_w (h : QuadricIntersectionModel.CFSTheorem28ii) :
    pairTwoEquiv h (coordinateW h true)=ThirdTwistField.PairTwo.w := by
  change Affine.PairTwo.fractionMap (fractionFieldRingEquiv h true
    (germ h true ((Charts.zSectionsRingEquiv true).symm (Affine.w true))))=_
  rw [fractionFieldRingEquiv_germ,RingEquiv.apply_symm_apply,
    Affine.PairTwo.fractionMap_algebraMap,Affine.PairTwo.coordinateMap_w]

end FunctionField
end
end Z2Z4Rank6.ThirdTwistPairGeometry
