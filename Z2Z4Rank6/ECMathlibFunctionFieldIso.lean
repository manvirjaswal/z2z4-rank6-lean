import Z2Z4Rank6.ECFunctionField
import Z2Z4Rank6.BaseFunctionFieldIso

/-!
# The printed cubic's field and Mathlib's coordinate function field

The quadratic presentation of Q(E_C) is identified with Mathlib's fraction
field of the affine Weierstrass coordinate ring. The coordinate map
uses the quotient universal property, its injectivity uses the two explicit
bases, and field generation proves surjectivity. Source: Jaswal, Lemma 4.1 and Theorem 1.2(a),
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.ECMathlibFunctionFieldIso
open Polynomial ECFunctionField
open WeierstrassCurve.Affine
open scoped Classical Polynomial.Bivariate
noncomputable section

abbrev CoordinateRing := EC.toAffine.CoordinateRing
abbrev MathlibField := EC.toAffine.FunctionField

def coefficientMap : ℚ[X] →+* ECFunctionField.K :=
  (algebraMap ECFunctionField.Base ECFunctionField.K).comp
    (algebraMap ℚ[X] ECFunctionField.Base)

theorem coefficientMap_eq (p : ℚ[X]) :
    coefficientMap p=algebraMap ECFunctionField.Base ECFunctionField.K
      (algebraMap ℚ[X] ECFunctionField.Base p) := rfl

def coordinateMap : CoordinateRing →+* ECFunctionField.K :=
  AdjoinRoot.lift coefficientMap ECFunctionField.y (by
    norm_num [WeierstrassCurve.Affine.polynomial,EC,coefficientMap,
      RingHom.comp_apply,RatFunc.algebraMap_X]
    simp only [Polynomial.eval₂_pow,Polynomial.eval₂_C]
    norm_num [RingHom.comp_apply,RatFunc.algebraMap_X]
    simp only [map_ofNat]
    have hy := ECFunctionField.y_sq
    dsimp only [ECFunctionField.x] at hy
    linear_combination hy)

@[simp] theorem coordinateMap_mk (p : ℚ[X][Y]) :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk EC.toAffine p)=
      p.eval₂ coefficientMap ECFunctionField.y :=
  AdjoinRoot.lift_mk _ _

@[simp] theorem coordinateMap_C (p : ℚ[X]) :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk EC.toAffine (C p))=
      coefficientMap p := by
  simp only [coordinateMap_mk,eval₂_C]

@[simp] theorem coordinateMap_Y :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk EC.toAffine Polynomial.X)=
      ECFunctionField.y := by
  simp only [coordinateMap_mk,eval₂_X]

theorem coordinateMap_injective : Function.Injective coordinateMap := by
  apply (injective_iff_map_eq_zero coordinateMap).mpr
  intro z hz
  obtain ⟨p,q,rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have he : algebraMap ECFunctionField.Base ECFunctionField.K
        (algebraMap ℚ[X] ECFunctionField.Base p)+
      algebraMap ECFunctionField.Base ECFunctionField.K
        (algebraMap ℚ[X] ECFunctionField.Base q)*ECFunctionField.y=0 := by
    simpa only [WeierstrassCurve.Affine.CoordinateRing.smul,map_add,map_mul,map_one,
      mul_one,coordinateMap_C,coordinateMap_Y,coefficientMap_eq] using hz
  have hp := congrArg QuadraticAlgebra.re he
  have hq := congrArg QuadraticAlgebra.im he
  simp [ECFunctionField.y] at hp hq
  simp only [hp,hq,zero_smul,zero_add]

def fieldMap : MathlibField →+* ECFunctionField.K :=
  IsFractionRing.lift coordinateMap_injective

@[simp] theorem fieldMap_coordinate (z : CoordinateRing) :
    fieldMap (algebraMap CoordinateRing MathlibField z)=coordinateMap z :=
  IsFractionRing.lift_algebraMap coordinateMap_injective z

def fieldAlgHom : MathlibField →ₐ[ℚ] ECFunctionField.K where
  toRingHom := fieldMap
  commutes' := fieldMap.map_rat_algebraMap

theorem fieldAlgHom_surjective : Function.Surjective fieldAlgHom := by
  have hx : ECFunctionField.x∈fieldAlgHom.fieldRange := by
    refine ⟨algebraMap CoordinateRing MathlibField
      (WeierstrassCurve.Affine.CoordinateRing.mk EC.toAffine (C Polynomial.X)),?_⟩
    change fieldMap _=ECFunctionField.x
    rw [fieldMap_coordinate,coordinateMap_C]
    rw [coefficientMap_eq,RatFunc.algebraMap_X]
    rfl
  have hy : ECFunctionField.y∈fieldAlgHom.fieldRange := by
    refine ⟨algebraMap CoordinateRing MathlibField
      (WeierstrassCurve.Affine.CoordinateRing.mk EC.toAffine Polynomial.X),?_⟩
    exact (fieldMap_coordinate _).trans coordinateMap_Y
  have hle : IntermediateField.adjoin ℚ
      ({ECFunctionField.x,ECFunctionField.y}:Set ECFunctionField.K)≤fieldAlgHom.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [ECFunctionField.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- An equivalence with Mathlib's coordinate fraction field. -/
def mathlibEquivQuadratic : MathlibField ≃ₐ[ℚ] ECFunctionField.K :=
  AlgEquiv.ofBijective fieldAlgHom ⟨fieldAlgHom.injective,fieldAlgHom_surjective⟩

/-- The constructed function field of C is an algebraic extension
isomorphic to the printed cubic's Mathlib function field. -/
def cFunctionFieldEquivMathlib : FunctionField.K ≃ₐ[ℚ] MathlibField :=
  BaseFunctionFieldIso.baseFunctionFieldEquiv.trans mathlibEquivQuadratic.symm

end
end Z2Z4Rank6.ECMathlibFunctionFieldIso
