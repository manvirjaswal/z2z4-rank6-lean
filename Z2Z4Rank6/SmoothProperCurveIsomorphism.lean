module

public import Z2Z4Rank6.StructureSheafCohomology
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Smooth proper curves are determined by their function fields

Source: Stacks Theorem 53.2.6 (tag 0BY1), categories (1)
and (6), gives the normal-proper-curve/function-field equivalence. Smoothness
over a field supplies regularity and normality by Lemma 33.25.4 (tag 056T).
The dimension-one, integral and proper premises make the schemes
curves in that theorem. Over Q every field RingEquiv automatically respects
the rational embeddings, as the proved coefficient lemma below shows.

The result is a Scheme isomorphism commuting with the structure
maps. The input is generic in the curves and their function fields.

-/
namespace Z2Z4Rank6
open AlgebraicGeometry CategoryTheory

/-- Published function-field criterion for smooth proper
integral rational curves, with an isomorphism over Spec Q as conclusion. -/
def SmoothProperCurveFunctionFieldIsomorphismTheorem : Prop :=
  ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (sX : X⟶StructureSheafCohomology.Base) (sY : Y⟶StructureSheafCohomology.Base),
    IsProper sX → IsProper sY → Smooth sX → Smooth sY →
      topologicalKrullDim X=1 → topologicalKrullDim Y=1 →
      (X.functionField≃+*Y.functionField) →
        Nonempty {i : X≅Y // i.hom≫sY=sX}

namespace SmoothProperCurveIsomorphism
noncomputable section

/-- The rational coefficient embedding in the generic-point
stalk field: coefficient map on global sections followed by the germ. -/
def qToFunctionField (X : Scheme.{0}) [IsIntegral X]
    (s : X⟶StructureSheafCohomology.Base) : ℚ→+*X.functionField := by
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X),trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.comp (StructureSheafCohomology.qToGlobal X s)

/-- Any field RingEquiv is automatically compatible with the two
rational coefficient maps. No arbitrary AlgebraQ instance is chosen. -/
theorem ringEquiv_rational_coefficients (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (sX : X⟶StructureSheafCohomology.Base) (sY : Y⟶StructureSheafCohomology.Base)
    (e : X.functionField≃+*Y.functionField) :
    e.toRingHom.comp (qToFunctionField X sX)=qToFunctionField Y sY :=
  RingHom.ext_rat _ _

theorem ringEquiv_rational_coefficients_apply (X Y : Scheme.{0})
    [IsIntegral X] [IsIntegral Y]
    (sX : X⟶StructureSheafCohomology.Base) (sY : Y⟶StructureSheafCohomology.Base)
    (e : X.functionField≃+*Y.functionField) (q : ℚ) :
    e (qToFunctionField X sX q)=qToFunctionField Y sY q :=
  DFunLike.congr_fun (ringEquiv_rational_coefficients X Y sX sY e) q

/-- Apply the published criterion. The output is a scheme isomorphism over Q. -/
theorem exists_overBase_iso (h : SmoothProperCurveFunctionFieldIsomorphismTheorem)
    (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (sX : X⟶StructureSheafCohomology.Base) (sY : Y⟶StructureSheafCohomology.Base)
    (hpX : IsProper sX) (hpY : IsProper sY) (hsX : Smooth sX) (hsY : Smooth sY)
    (hdX : topologicalKrullDim X=1) (hdY : topologicalKrullDim Y=1)
    (e : X.functionField≃+*Y.functionField) :
    Nonempty {i : X≅Y // i.hom≫sY=sX} :=
  h X Y sX sY hpX hpY hsX hsY hdX hdY e

/-- Select an isomorphism over Q from the published input and the geometric and field data. -/
def overBaseIso (h : SmoothProperCurveFunctionFieldIsomorphismTheorem)
    (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (sX : X⟶StructureSheafCohomology.Base) (sY : Y⟶StructureSheafCohomology.Base)
    (hpX : IsProper sX) (hpY : IsProper sY) (hsX : Smooth sX) (hsY : Smooth sY)
    (hdX : topologicalKrullDim X=1) (hdY : topologicalKrullDim Y=1)
    (e : X.functionField≃+*Y.functionField) : {i : X≅Y // i.hom≫sY=sX} :=
  Classical.choice (exists_overBase_iso h X Y sX sY hpX hpY hsX hsY hdX hdY e)

end
end SmoothProperCurveIsomorphism
end Z2Z4Rank6
