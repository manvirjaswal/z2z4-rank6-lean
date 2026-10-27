module

public import Common.Elliptic.WeierstrassSchemeVariableChangeAlgebra
public import Common.AlgebraicGeometry.ProjGradedIsomorphism

@[expose] public section

/-!
# Scheme isomorphisms for admissible Weierstrass changes

The isomorphism is induced by the proved mutually inverse graded maps of the
homogeneous quotient rings. Over Q its compatibility with the rational
structure maps also follows directly from uniqueness of rational ring maps.
-/

namespace WeierstrassScheme.VariableChange
noncomputable section
open AlgebraicGeometry CategoryTheory
universe u
variable {K : Type u} [Field K] [Infinite K]

/-- Projective scheme isomorphism for an admissible change. -/
def schemeIso (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    scheme (c • W) ≅ scheme W :=
  Proj.isoOfInverse (gradedMap W c) (gradedInverse W c)
    (gradedInverse_comp_gradedMap W c) (gradedMap_comp_gradedInverse W c)

/-- The coordinate change respects the structure maps over any
infinite ground field. -/
theorem schemeIso_over (W : WeierstrassCurve K)
    (c : WeierstrassCurve.VariableChange K) :
    (schemeIso W c).hom ≫ structureMap W = structureMap (c • W) := by
  have hcoef : CommRingCat.ofHom (algebraMap K (grading W 0)) ≫
      CommRingCat.ofHom (gradedMap W c).gradedZeroRingHom =
      CommRingCat.ofHom (algebraMap K (grading (c • W) 0)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro q
    apply Subtype.ext
    exact (quotientMap W c).commutes q
  change Proj.map (gradedMap W c) _ ≫
      (Proj.toSpecZero (grading W) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (grading W 0)))) =
    Proj.toSpecZero (grading (c • W)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (grading (c • W) 0)))
  rw [←Category.assoc, Proj.map_toSpecZero, Category.assoc, ←Spec.map_comp, hcoef]

/-- The cubic isomorphism respects the rational structure maps. -/
theorem schemeIso_over_rat (W : WeierstrassCurve ℚ)
    (c : WeierstrassCurve.VariableChange ℚ) :
    (schemeIso W c).hom ≫ structureMap W = structureMap (c • W) := by
  exact schemeIso_over W c

/-- The inverse isomorphism also respects the rational structure. -/
theorem schemeIso_inv_over_rat (W : WeierstrassCurve ℚ)
    (c : WeierstrassCurve.VariableChange ℚ) :
    (schemeIso W c).inv ≫ structureMap (c • W) = structureMap W := by
  rw [←schemeIso_over_rat W c, ←Category.assoc]
  simp

def overBaseIso (W : WeierstrassCurve K) (c : WeierstrassCurve.VariableChange K) :
    {i : scheme (c • W) ≅ scheme W //
      i.hom ≫ structureMap W = structureMap (c • W)} :=
  ⟨schemeIso W c, schemeIso_over W c⟩

end
end WeierstrassScheme.VariableChange
