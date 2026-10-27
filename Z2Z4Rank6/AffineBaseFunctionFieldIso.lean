import Z2Z4Rank6.AffineBaseFunctionFieldIsoCoordinate
import Mathlib.RingTheory.Localization.FractionRing

/-! The fraction field of Q[M,U,V]/(U²−15M²−1210,V²−10M²−1215)
is the constructed degree-four Q(C). Injectivity and the domain instance are
proved by polynomial quadratic normal forms; surjectivity follows from the
three field generators. Source: Jaswal (1.3), Theorem 1.2(a),
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section
abbrev AffineField := FractionRing CoordinateRing

def fractionMapRing : AffineField→+*FunctionField.K :=
  IsFractionRing.lift coordinateMap_injective

def fractionMap : AffineField→ₐ[ℚ]FunctionField.K where
  __ := fractionMapRing
  commutes' := fractionMapRing.map_rat_algebraMap

@[simp] theorem fractionMap_algebraMap (z : CoordinateRing) :
    fractionMap (algebraMap CoordinateRing AffineField z)=coordinateMap z :=
  IsFractionRing.lift_algebraMap coordinateMap_injective z

@[simp] theorem fractionMap_m :
    fractionMap (algebraMap CoordinateRing AffineField AffineBaseScheme.m)=FunctionField.m := by
  rw [fractionMap_algebraMap,coordinateMap_m]
@[simp] theorem fractionMap_u :
    fractionMap (algebraMap CoordinateRing AffineField AffineBaseScheme.u)=FunctionField.u := by
  rw [fractionMap_algebraMap,coordinateMap_u]
@[simp] theorem fractionMap_v :
    fractionMap (algebraMap CoordinateRing AffineField AffineBaseScheme.v)=FunctionField.v := by
  rw [fractionMap_algebraMap,coordinateMap_v]

theorem fractionMap_surjective : Function.Surjective fractionMap := by
  have hm : FunctionField.m∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField AffineBaseScheme.m,fractionMap_m⟩
  have hu : FunctionField.u∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField AffineBaseScheme.u,fractionMap_u⟩
  have hv : FunctionField.v∈fractionMap.fieldRange :=
    ⟨algebraMap CoordinateRing AffineField AffineBaseScheme.v,fractionMap_v⟩
  have hle : IntermediateField.adjoin ℚ
      ({FunctionField.m,FunctionField.u,FunctionField.v}:Set FunctionField.K)≤fractionMap.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl|rfl
    · exact hm
    · exact hu
    · exact hv
  rw [FunctionField.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- An algebra equivalence from the affine coordinate ring's
fraction field to the existing explicit Q(m,u,v). -/
def affineFunctionFieldEquiv : FractionRing AffineBaseScheme.CoordinateRing ≃ₐ[ℚ] FunctionField.K :=
  AlgEquiv.ofBijective fractionMap ⟨fractionMap.injective,fractionMap_surjective⟩

@[simp] theorem affineFunctionFieldEquiv_m :
    affineFunctionFieldEquiv (algebraMap CoordinateRing AffineField AffineBaseScheme.m)=FunctionField.m :=
  fractionMap_m
@[simp] theorem affineFunctionFieldEquiv_u :
    affineFunctionFieldEquiv (algebraMap CoordinateRing AffineField AffineBaseScheme.u)=FunctionField.u :=
  fractionMap_u
@[simp] theorem affineFunctionFieldEquiv_v :
    affineFunctionFieldEquiv (algebraMap CoordinateRing AffineField AffineBaseScheme.v)=FunctionField.v :=
  fractionMap_v
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
