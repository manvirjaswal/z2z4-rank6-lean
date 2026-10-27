module

public import Z2Z4Rank6.ECProjectiveSchemeFunctionField
public import Z2Z4Rank6.ECProjectiveSchemeDimension
public import Z2Z4Rank6.ProjectiveBaseSchemeDimension
public import Z2Z4Rank6.ProjectiveBaseSchemeRationalPoints
public import Z2Z4Rank6.ECProjectiveSchemeRationalPoints
public import Z2Z4Rank6.SmoothProperCurveIsomorphism

@[expose] public section

/-!
# The projective base is Q-isomorphic to the printed cubic

Jaswal, Lemma 4.1(b), Theorem 1.2(a), DOI 10.5281/zenodo.23437117.
Both objects are displayed homogeneous quotient Proj schemes.
Their properness, smoothness, integrality and dimension 1 are proved.
The generic-point stalk fields have a proved Q-algebra equivalence.
The hypothesis below is the smooth-proper-curve/function-field theorem, Stacks 53.2.6 (tag 0BY1).
Its conclusion is a scheme
isomorphism commuting with the rational structure maps.

This establishes the geometric curve isomorphism.
-/

namespace Z2Z4Rank6.BaseProjectiveSchemeIsomorphism
noncomputable section
open AlgebraicGeometry CategoryTheory

/-- An isomorphism between the two displayed projective schemes,
with its over-Q equation retained in the type. -/
def overBaseIso (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    {i : ProjectiveBaseScheme.scheme≅ECProjectiveScheme.scheme //
      i.hom≫ECProjectiveScheme.structureMap=ProjectiveBaseScheme.structureMap} :=
  SmoothProperCurveIsomorphism.overBaseIso h
    ProjectiveBaseScheme.scheme ECProjectiveScheme.scheme
    ProjectiveBaseScheme.structureMap ECProjectiveScheme.structureMap
    inferInstance inferInstance
    ProjectiveBaseScheme.structureMap_smooth_morphism
    ECProjectiveScheme.structureMap_smooth_morphism
    ProjectiveBaseScheme.scheme_topologicalKrullDim
    ECProjectiveScheme.scheme_topologicalKrullDim
    ECProjectiveSchemeFunctionField.baseProjectiveFunctionFieldEquiv.toRingEquiv

def schemeIso (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    ProjectiveBaseScheme.scheme≅ECProjectiveScheme.scheme := (overBaseIso h).val

theorem schemeIso_over (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    (schemeIso h).hom≫ECProjectiveScheme.structureMap=ProjectiveBaseScheme.structureMap :=
  (overBaseIso h).property

theorem schemeIso_inv_over (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    (schemeIso h).inv≫ProjectiveBaseScheme.structureMap=ECProjectiveScheme.structureMap := by
  rw [←schemeIso_over h,←Category.assoc]
  simp

/-- The scheme-isomorphism component of the printed precise theorem. -/
theorem theorem_1_2_a_isomorphism (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    Nonempty {i : ProjectiveBaseScheme.scheme≅ECProjectiveScheme.scheme //
      i.hom≫ECProjectiveScheme.structureMap=ProjectiveBaseScheme.structureMap} :=
  ⟨overBaseIso h⟩

/-- Spec Q rational points transported by the scheme isomorphism. -/
def schemePointEquiv (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    ProjectiveBaseSchemeRationalPoints.RationalPoint≃
      ECProjectiveSchemeRationalPoints.RationalPoint where
  toFun p := ⟨p.val≫(schemeIso h).hom,by rw [Category.assoc,schemeIso_over];exact p.property⟩
  invFun p := ⟨p.val≫(schemeIso h).inv,by rw [Category.assoc,schemeIso_inv_over];exact p.property⟩
  left_inv p := Subtype.ext (by simp [Category.assoc])
  right_inv p := Subtype.ext (by simp [Category.assoc])

/-- All affine rational C-points correspond to the Mathlib rational
point group of the printed EC, through the two projective schemes. -/
def rationalPointEquiv (h : SmoothProperCurveFunctionFieldIsomorphismTheorem) :
    CPoint≃RationalPoints EC :=
  (ProjectiveBaseSchemeRationalPoints.rationalPointEquiv.trans (schemePointEquiv h)).trans
    ECProjectiveSchemeRationalPoints.rationalPointEquiv.symm

end
end Z2Z4Rank6.BaseProjectiveSchemeIsomorphism
