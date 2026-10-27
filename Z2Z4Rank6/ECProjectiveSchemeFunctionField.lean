module

public import Z2Z4Rank6.ECProjectiveSchemeIntegral
public import Z2Z4Rank6.ProjectiveBaseSchemeFunctionField
public import Z2Z4Rank6.StructureSheafCohomology
public import Z2Z4Rank6.ECProjectiveAffineFunctionField
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
explicit quadratic EC function field, and then with the Mathlib
Weierstrass function field of the printed cubic.
-/
namespace Z2Z4Rank6.ECProjectiveSchemeFunctionField
noncomputable section
open scoped Classical
open AlgebraicGeometry CategoryTheory
open ECProjectiveScheme ECProjectiveSchemeCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ActualField := scheme.functionField
abbrev AffineField := FractionRing ECProjectiveSchemeAffine.CoordinateRing

instance zChart_nonempty : Nonempty zOpen :=
  ⟨⟨chart_overlap_nonempty.choose,chart_overlap_nonempty.choose_spec.1⟩⟩

theorem zChart_affine : IsAffineOpen zOpen :=
  Proj.isAffineOpen_basicOpen grading z (coordinate_degree 2) (by decide : 0<1)

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

def zGammaIso : CommRingCat.of ECProjectiveSchemeAffine.CoordinateRing ≅ Γ(scheme,zOpen) :=
  zChartRingEquiv.symm.toRingEquiv.toCommRingCatIso ≪≫
    Proj.basicOpenIsoAway grading z (coordinate_degree 2) (by decide : 0<1)

def zSectionsRingEquiv : ↥Γ(scheme,zOpen) ≃+* ECProjectiveSchemeAffine.CoordinateRing :=
  zGammaIso.symm.commRingCatIsoToRingEquiv

/-- The generic-point stalk is the affine chart's fraction field. -/
def fractionFieldRingEquiv : ActualField ≃+* AffineField :=
  IsLocalization.ringEquivOfRingEquiv ActualField AffineField zSectionsRingEquiv
    (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv)

@[simp] theorem fractionFieldRingEquiv_germ (a : Γ(scheme,zOpen)) :
    fractionFieldRingEquiv (scheme.germToFunctionField zOpen a)=
      algebraMap ECProjectiveSchemeAffine.CoordinateRing AffineField (zSectionsRingEquiv a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (S:=ActualField) (Q:=AffineField)
    (j:=zSectionsRingEquiv) (MulEquivClass.map_nonZeroDivisors zSectionsRingEquiv) a

/-- Projective generic-point stalk identified with the explicit quadratic EC field. -/
def functionFieldEquiv : ActualField ≃ₐ[ℚ] ECFunctionField.K :=
  {fractionFieldRingEquiv.trans ECProjectiveAffineFunctionField.affineFunctionFieldEquiv.toRingEquiv with
    commutes' := (fractionFieldRingEquiv.trans
      ECProjectiveAffineFunctionField.affineFunctionFieldEquiv.toRingEquiv).toRingHom.map_rat_algebraMap}

@[simp] theorem functionFieldEquiv_germ (a : Γ(scheme,zOpen)) :
    functionFieldEquiv (scheme.germToFunctionField zOpen a)=
      ECProjectiveAffineFunctionField.coordinateMap (zSectionsRingEquiv a) := by
  change ECProjectiveAffineFunctionField.affineFunctionFieldEquiv
    (fractionFieldRingEquiv (scheme.germToFunctionField zOpen a))=_
  rw [fractionFieldRingEquiv_germ]
  exact ECProjectiveAffineFunctionField.fractionMap_algebraMap _

@[simp] theorem functionFieldEquiv_coefficient (q : ℚ) :
    functionFieldEquiv (actualCoefficientMap q)=algebraMap ℚ ECFunctionField.K q := by
  rw [actualCoefficientMap_eq]
  exact functionFieldEquiv.commutes q

/-- Generic germs of the affine Weierstrass coordinates. -/
def coordinateX : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm ECProjectiveSchemeAffine.x)
def coordinateY : ActualField := scheme.germToFunctionField zOpen
  (zSectionsRingEquiv.symm ECProjectiveSchemeAffine.y)

@[simp] theorem functionFieldEquiv_x : functionFieldEquiv coordinateX=ECFunctionField.x := by
  dsimp only [coordinateX]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,
    ECProjectiveAffineFunctionField.coordinateMap_x]
@[simp] theorem functionFieldEquiv_y : functionFieldEquiv coordinateY=ECFunctionField.y := by
  dsimp only [coordinateY]
  rw [functionFieldEquiv_germ,RingEquiv.apply_symm_apply,
    ECProjectiveAffineFunctionField.coordinateMap_y]

/-- The projective generic-point stalk is identified with the printed cubic's
Mathlib Weierstrass affine function field. The result is an equivalence of
fields; complete-curve scheme isomorphisms are constructed separately. -/
def mathlibECFunctionFieldEquiv : ActualField ≃ₐ[ℚ] EC.toAffine.FunctionField :=
  functionFieldEquiv.trans ECMathlibFunctionFieldIso.mathlibEquivQuadratic.symm

/-- The two projective schemes have Q-isomorphic generic-point stalks.
This is a field equivalence only; extension to a scheme isomorphism is separate. -/
def baseProjectiveFunctionFieldEquiv : ProjectiveBaseScheme.scheme.functionField ≃ₐ[ℚ] ActualField :=
  ProjectiveBaseSchemeFunctionField.mathlibECFunctionFieldEquiv.trans mathlibECFunctionFieldEquiv.symm

end
end Z2Z4Rank6.ECProjectiveSchemeFunctionField
