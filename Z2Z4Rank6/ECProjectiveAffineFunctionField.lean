module

public import Z2Z4Rank6.ECProjectiveAffineCoordinate
public import Z2Z4Rank6.ECMathlibFunctionFieldIso
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

/-! The fraction field of the affine chart of the printed projective
EC cubic is the explicit quadratic EC field, and hence Mathlib's
Weierstrass function field.
Source: Jaswal, Theorem 1.2(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.ECProjectiveAffineFunctionField
noncomputable section
abbrev AffineField := FractionRing CoordinateRing

def fractionMapRing : AffineField→+*ECFunctionField.K := IsFractionRing.lift coordinateMap_injective

def fractionMap : AffineField→ₐ[ℚ]ECFunctionField.K where
  __ := fractionMapRing
  commutes' := fractionMapRing.map_rat_algebraMap

@[simp] theorem fractionMap_algebraMap (z : CoordinateRing) :
    fractionMap (algebraMap CoordinateRing AffineField z)=coordinateMap z :=
  IsFractionRing.lift_algebraMap coordinateMap_injective z
@[simp] theorem fractionMap_x :
    fractionMap (algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.x)=ECFunctionField.x := by
  rw [fractionMap_algebraMap,coordinateMap_x]
@[simp] theorem fractionMap_y :
    fractionMap (algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.y)=ECFunctionField.y := by
  rw [fractionMap_algebraMap,coordinateMap_y]

theorem fractionMap_surjective : Function.Surjective fractionMap := by
  have hx : ECFunctionField.x∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.x,fractionMap_x⟩
  have hy : ECFunctionField.y∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.y,fractionMap_y⟩
  have hle : IntermediateField.adjoin ℚ ({ECFunctionField.x,ECFunctionField.y}:Set ECFunctionField.K)≤fractionMap.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl
    · exact hx
    · exact hy
  rw [ECFunctionField.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- The affine projective-cubic chart field, with the original
quotient ring as source. -/
def affineFunctionFieldEquiv : FractionRing ECProjectiveSchemeAffine.CoordinateRing≃ₐ[ℚ]ECFunctionField.K :=
  AlgEquiv.ofBijective fractionMap ⟨fractionMap.injective,fractionMap_surjective⟩
@[simp] theorem affineFunctionFieldEquiv_x :
    affineFunctionFieldEquiv (algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.x)=ECFunctionField.x :=
  fractionMap_x
@[simp] theorem affineFunctionFieldEquiv_y :
    affineFunctionFieldEquiv (algebraMap CoordinateRing AffineField ECProjectiveSchemeAffine.y)=ECFunctionField.y :=
  fractionMap_y

/-- Composition with the separately constructed Mathlib coordinate
function-field equivalence. -/
def affineFunctionFieldEquivMathlib : FractionRing ECProjectiveSchemeAffine.CoordinateRing≃ₐ[ℚ]
    EC.toAffine.FunctionField :=
  affineFunctionFieldEquiv.trans ECMathlibFunctionFieldIso.mathlibEquivQuadratic.symm
end
end Z2Z4Rank6.ECProjectiveAffineFunctionField
