import Common.AlgebraicGeometry.ProjFieldPoint
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Projectivity over a field

Projective n-space is the Proj of the standard graded polynomial
ring on n+1 variables. Projectivity retains a closed immersion
into one of these spaces, over the specified field.

Reference: EGA II, Definition 5.5.2 (projective morphisms), specialized
to a field, where a finite-type projective bundle is an ordinary P^n.
-/
namespace Common.AlgebraicGeometry.ProjectiveScheme
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k] (n : ℕ)

abbrev Ring := MvPolynomial (Fin (n+1)) k

def grading : ℕ → Submodule k (Ring k n) :=
  MvPolynomial.homogeneousSubmodule (Fin (n+1)) k

instance gradedAlgebra : GradedAlgebra (grading k n) := MvPolynomial.gradedAlgebra

instance gradeZero_scalarTower : IsScalarTower k (grading k n 0) (Ring k n) :=
  IsScalarTower.of_algebraMap_eq' (R:=k) (S:=grading k n 0) (A:=Ring k n) rfl

def space : Scheme := Proj (grading k n)

def structureMap : space k n ⟶ Spec (CommRingCat.of k) :=
  ProjFieldPoint.structureMap (grading k n)

/-- A projective embedding, with its field-linearity equation. -/
structure Embedding (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) where
  dimension : ℕ
  hom : X ⟶ space k dimension
  closed : IsClosedImmersion hom
  over : hom≫structureMap k dimension=s

def IsProjective (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  Nonempty (Embedding k X s)

end
end Common.AlgebraicGeometry.ProjectiveScheme
