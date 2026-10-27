import Z2Z4Rank6.SecondJacobianFunctionField
import Z2Z4Rank6.SecondJacobianBasic

/-!
# The printed second cubic's field and Mathlib's coordinate function field

The quadratic presentation of Q(J₂) is identified with Mathlib's fraction
field of the affine Weierstrass coordinate ring. The coordinate map
uses the quotient universal property, its injectivity uses the two explicit
bases, and field generation proves surjectivity. Source: Jaswal, Theorem 8.1(a),
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.SecondMathlibFunctionFieldIso
open Polynomial SecondJacobianFunctionField
open WeierstrassCurve.Affine
open scoped Classical Polynomial.Bivariate
noncomputable section

abbrev CoordinateRing := J2.toAffine.CoordinateRing
abbrev MathlibField := J2.toAffine.FunctionField

def coefficientMap : ℚ[X] →+* SecondJacobianFunctionField.K :=
  (algebraMap SecondJacobianFunctionField.Base SecondJacobianFunctionField.K).comp
    (algebraMap ℚ[X] SecondJacobianFunctionField.Base)

theorem coefficientMap_eq (p : ℚ[X]) :
    coefficientMap p=algebraMap SecondJacobianFunctionField.Base SecondJacobianFunctionField.K
      (algebraMap ℚ[X] SecondJacobianFunctionField.Base p) := rfl

def coordinateMap : CoordinateRing →+* SecondJacobianFunctionField.K :=
  AdjoinRoot.lift coefficientMap SecondJacobianFunctionField.y (by
    norm_num [WeierstrassCurve.Affine.polynomial,J2,coefficientMap,
      RingHom.comp_apply,RatFunc.algebraMap_X]
    simp only [Polynomial.eval₂_pow,Polynomial.eval₂_C]
    norm_num [RingHom.comp_apply,RatFunc.algebraMap_X]
    simp only [map_ofNat]
    have hy := SecondJacobianFunctionField.y_sq
    dsimp only [SecondJacobianFunctionField.x] at hy
    linear_combination hy)

@[simp] theorem coordinateMap_mk (p : ℚ[X][Y]) :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk J2.toAffine p)=
      p.eval₂ coefficientMap SecondJacobianFunctionField.y :=
  AdjoinRoot.lift_mk _ _

@[simp] theorem coordinateMap_C (p : ℚ[X]) :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk J2.toAffine (C p))=
      coefficientMap p := by
  simp only [coordinateMap_mk,eval₂_C]

@[simp] theorem coordinateMap_Y :
    coordinateMap (WeierstrassCurve.Affine.CoordinateRing.mk J2.toAffine Polynomial.X)=
      SecondJacobianFunctionField.y := by
  simp only [coordinateMap_mk,eval₂_X]

theorem coordinateMap_injective : Function.Injective coordinateMap := by
  apply (injective_iff_map_eq_zero coordinateMap).mpr
  intro z hz
  obtain ⟨p,q,rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq z
  have he : algebraMap SecondJacobianFunctionField.Base SecondJacobianFunctionField.K
        (algebraMap ℚ[X] SecondJacobianFunctionField.Base p)+
      algebraMap SecondJacobianFunctionField.Base SecondJacobianFunctionField.K
        (algebraMap ℚ[X] SecondJacobianFunctionField.Base q)*SecondJacobianFunctionField.y=0 := by
    simpa only [WeierstrassCurve.Affine.CoordinateRing.smul,map_add,map_mul,map_one,
      mul_one,coordinateMap_C,coordinateMap_Y,coefficientMap_eq] using hz
  have hp := congrArg QuadraticAlgebra.re he
  have hq := congrArg QuadraticAlgebra.im he
  simp [SecondJacobianFunctionField.y] at hp hq
  simp only [hp,hq,zero_smul,zero_add]

def fieldMap : MathlibField →+* SecondJacobianFunctionField.K :=
  IsFractionRing.lift coordinateMap_injective

@[simp] theorem fieldMap_coordinate (z : CoordinateRing) :
    fieldMap (algebraMap CoordinateRing MathlibField z)=coordinateMap z :=
  IsFractionRing.lift_algebraMap coordinateMap_injective z

def fieldAlgHom : MathlibField →ₐ[ℚ] SecondJacobianFunctionField.K where
  toRingHom := fieldMap
  commutes' := fieldMap.map_rat_algebraMap

theorem fieldAlgHom_surjective : Function.Surjective fieldAlgHom := by
  have hx : SecondJacobianFunctionField.x∈fieldAlgHom.fieldRange := by
    refine ⟨algebraMap CoordinateRing MathlibField
      (WeierstrassCurve.Affine.CoordinateRing.mk J2.toAffine (C Polynomial.X)),?_⟩
    change fieldMap _=SecondJacobianFunctionField.x
    rw [fieldMap_coordinate,coordinateMap_C]
    rw [coefficientMap_eq,RatFunc.algebraMap_X]
    rfl
  have hy : SecondJacobianFunctionField.y∈fieldAlgHom.fieldRange := by
    refine ⟨algebraMap CoordinateRing MathlibField
      (WeierstrassCurve.Affine.CoordinateRing.mk J2.toAffine Polynomial.X),?_⟩
    exact (fieldMap_coordinate _).trans coordinateMap_Y
  have hle : IntermediateField.adjoin ℚ
      ({SecondJacobianFunctionField.x,SecondJacobianFunctionField.y}:Set SecondJacobianFunctionField.K)≤fieldAlgHom.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  rw [SecondJacobianFunctionField.field_adjoin_coordinates_eq_top] at hle
  intro z
  exact hle (by trivial)

/-- An equivalence with Mathlib's coordinate fraction field. -/
def mathlibEquivQuadratic : MathlibField ≃ₐ[ℚ] SecondJacobianFunctionField.K :=
  AlgEquiv.ofBijective fieldAlgHom ⟨fieldAlgHom.injective,fieldAlgHom_surjective⟩

end
end Z2Z4Rank6.SecondMathlibFunctionFieldIso
