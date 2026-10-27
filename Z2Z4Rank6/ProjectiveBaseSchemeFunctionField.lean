module

public import Z2Z4Rank6.ProjectiveBaseSchemeIntegral
public import Z2Z4Rank6.ProjectiveBaseSchemeSections
public import Z2Z4Rank6.AffineBaseFunctionFieldIso
public import Z2Z4Rank6.ECMathlibFunctionFieldIso
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

/-!
# The projective scheme function field

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a), Theorem 1.2(a).
Mathlib defines the function field as the generic-point stalk. The
nonempty affine z-chart makes that stalk the fraction field of its
section ring. The proved chart-ring and affine fraction-field equivalences
therefore identify the projective scheme function field with the
explicit degree-four field Q(m,u,v), and then with the Mathlib
Weierstrass function field of the printed cubic.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeFunctionField
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeSections
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ActualField := scheme.functionField
abbrev AffineField := FractionRing AffineBaseScheme.CoordinateRing

instance zChart_nonempty : Nonempty zOpen :=
  ⟨⟨chart_overlap_nonempty.choose,chart_overlap_nonempty.choose_spec.1⟩⟩

theorem zChart_affine : IsAffineOpen zOpen :=
  Proj.isAffineOpen_basicOpen grading z (coordinate_degree 3) (by decide : 0<1)

instance actualField_isFractionRing : IsFractionRing Γ(scheme,zOpen) ActualField :=
  functionField_isFractionRing_of_isAffineOpen scheme zOpen zChart_affine

instance top_nonempty : Nonempty (⊤ : scheme.Opens) :=
  ⟨⟨chart_overlap_nonempty.choose,trivial⟩⟩

/-- The coefficient map induced by the scheme structure morphism. -/
def actualCoefficientMap : ℚ →+* ActualField :=
  (scheme.germToFunctionField ⊤).hom.comp (StructureSheafCohomology.qToGlobal scheme structureMap)

instance actualFieldRationalAlgebra : Algebra ℚ ActualField := actualCoefficientMap.toAlgebra

theorem actualCoefficientMap_eq : actualCoefficientMap=algebraMap ℚ ActualField :=
  RingHom.ext_rat _ _

/-- The generic-point stalk is the affine chart's fraction field. -/
def fractionFieldRingEquiv : ActualField ≃+* AffineField :=
  IsLocalization.ringEquivOfRingEquiv ActualField AffineField zSectionsRingEquiv
    (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv)

@[simp] theorem fractionFieldRingEquiv_germ (a : Γ(scheme,zOpen)) :
    fractionFieldRingEquiv (scheme.germToFunctionField zOpen a)=
      algebraMap AffineBaseScheme.CoordinateRing AffineField (zSectionsRingEquiv a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S:=ActualField) (Q:=AffineField)
    (j:=zSectionsRingEquiv) (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv) a

/-- Projective generic-point stalk identified with Q(m,u,v). -/
def functionFieldEquiv : ActualField ≃ₐ[ℚ] FunctionField.K :=
  {fractionFieldRingEquiv.trans AffineBaseFunctionFieldIso.affineFunctionFieldEquiv.toRingEquiv with
    commutes' := (fractionFieldRingEquiv.trans
      AffineBaseFunctionFieldIso.affineFunctionFieldEquiv.toRingEquiv).toRingHom.map_rat_algebraMap}

@[simp] theorem functionFieldEquiv_germ (a : Γ(scheme,zOpen)) :
    functionFieldEquiv (scheme.germToFunctionField zOpen a)=
      AffineBaseFunctionFieldIso.coordinateMap (zSectionsRingEquiv a) := by
  change AffineBaseFunctionFieldIso.affineFunctionFieldEquiv
    (fractionFieldRingEquiv (scheme.germToFunctionField zOpen a))=_
  rw [fractionFieldRingEquiv_germ]
  exact AffineBaseFunctionFieldIso.fractionMap_algebraMap _

@[simp] theorem functionFieldEquiv_coefficient (q : ℚ) :
    functionFieldEquiv (actualCoefficientMap q)=algebraMap ℚ FunctionField.K q := by
  rw [actualCoefficientMap_eq]
  exact functionFieldEquiv.commutes q

/-- Rational functions obtained by taking the germs of the displayed coordinates. -/
def coordinateM : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm AffineBaseScheme.m)
def coordinateU : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm AffineBaseScheme.u)
def coordinateV : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm AffineBaseScheme.v)

@[simp] theorem functionFieldEquiv_m : functionFieldEquiv coordinateM=FunctionField.m := by
  dsimp only [coordinateM]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,
    AffineBaseFunctionFieldIso.coordinateMap_m]
@[simp] theorem functionFieldEquiv_u : functionFieldEquiv coordinateU=FunctionField.u := by
  dsimp only [coordinateU]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,
    AffineBaseFunctionFieldIso.coordinateMap_u]
@[simp] theorem functionFieldEquiv_v : functionFieldEquiv coordinateV=FunctionField.v := by
  dsimp only [coordinateV]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,
    AffineBaseFunctionFieldIso.coordinateMap_v]

/-- The projective generic-point stalk is identified with the printed cubic's
Mathlib Weierstrass affine function field. The result is an equivalence of
fields; complete-curve scheme isomorphisms are constructed separately. -/
def mathlibECFunctionFieldEquiv : ActualField ≃ₐ[ℚ] EC.toAffine.FunctionField :=
  functionFieldEquiv.trans ECMathlibFunctionFieldIso.cFunctionFieldEquivMathlib

end
end Z2Z4Rank6.ProjectiveBaseSchemeFunctionField
