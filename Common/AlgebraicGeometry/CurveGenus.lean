module

public import Common.AlgebraicGeometry.RationalStructureSheafCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Genus one over the rationals

The predicate below spells out the usual smooth proper geometrically integral
curve and arithmetic genus conditions using schemes, structure maps,
canonical global constants and structure-sheaf cohomology. The genus convention
is Stacks Project, Definition 53.8.1 (tag 0BY6). The H1 object is Ext1 in the
category of rational module sheaves, with its canonical rational scalar action.
-/

namespace AlgebraicGeometry.RationalCurveGenus
open CategoryTheory RationalStructureSheafCohomology

/-- Smooth proper geometrically integral rational curve of genus one. -/
structure IsSmoothProperGenusOne (X : Scheme.{0}) (s : X ⟶ Base) : Prop where
  proper : IsProper s
  smooth : SmoothOfRelativeDimension 1 s
  geometricallyIntegral : GeometricallyIntegral s
  dimension : topologicalKrullDim X = 1
  constants : Function.Bijective (qToGlobal X s)
  finiteDimensional : FiniteDimensional ℚ (H1 X s)
  genus : Module.finrank ℚ (H1 X s) = 1

end AlgebraicGeometry.RationalCurveGenus
