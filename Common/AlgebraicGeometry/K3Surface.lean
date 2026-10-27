module

public import Common.AlgebraicGeometry.AffineDifferentialForms
public import Common.AlgebraicGeometry.StructureSheafCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

@[expose] public section

/-!
# K3 surfaces over a field

A K3 surface is a smooth proper geometrically integral surface with
trivial canonical bundle and vanishing first structure-sheaf
cohomology. Canonical triviality is expressed using top Kähler
differentials on the affine basis, and H1 is the Ext cohomology
object. None of these conditions is replaced by an assigned number.

Reference: Schütt–Shioda, *Elliptic Surfaces*, arXiv:0907.0298v3,
Definition 12.1, p. 59. The affine formulation of canonical triviality
uses Stacks, Lemma 29.33.5 and Remark 29.33.6 (tag 01UM).
-/

namespace Common.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
noncomputable section

variable (k : Type) [Field k]

/-- K3 conditions on a scheme over a field. -/
structure IsK3 (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k)) : Prop where
  proper : IsProper s
  smooth : SmoothOfRelativeDimension 2 s
  geometricallyIntegral : GeometricallyIntegral s
  dimension : topologicalKrullDim X = 2
  canonical : AffineDifferentialForms.HasTrivialCanonical k X s 2
  h1_vanishes : Subsingleton (StructureSheafCohomology.Cohomology k X s 1)

/-- The defining canonical trivialization of a K3 surface uses
coordinate-linear equivalences on every affine open. -/
theorem IsK3.canonicalTrivialization {X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of k)} (h : IsK3 k X s) :
    Nonempty (AffineDifferentialForms.CanonicalTrivialization k X s 2) :=
  h.canonical

/-- Vanishing means that every H1 class is zero. -/
theorem IsK3.h1_eq_zero {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of k)}
    (h : IsK3 k X s) (a : StructureSheafCohomology.Cohomology k X s 1) : a = 0 := by
  let := h.h1_vanishes
  exact Subsingleton.elim _ _

end
end Common.AlgebraicGeometry
