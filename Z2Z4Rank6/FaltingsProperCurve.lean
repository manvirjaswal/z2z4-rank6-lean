module

public import Z2Z4Rank6.SmoothProperGeometricIntegrality
public import Mathlib.Topology.KrullDimension

@[expose] public section

/-!
# Faltings finiteness for proper rational curves

Source: M. Stoll, Rational points on curves,
19 September 2015, §1.1, Theorem 1.1, p. 1, states Faltings finiteness for smooth
projective absolutely irreducible curves over Q of genus at least 2.
The proper version follows from Stacks 53.2.6 (tag 0BY1), categories (6)/(3),
and smooth normality (056T). Genus is the structure-sheaf H1 dimension
under the displayed conditions, Stacks 53.8.1 (in 0BY6), with the
rational-sheaf/Ext interpretation from 0B3A/03FD.
-/
namespace Z2Z4Rank6
open AlgebraicGeometry CategoryTheory

/-- Published proper-curve form of Faltings over Q, expressed using
cohomology and rational scheme morphisms over Spec Q. -/
def FaltingsProperCurveTheorem : Prop :=
  ∀ (X : Scheme.{0}) (s : X⟶StructureSheafCohomology.Base),
    IsProper s → Smooth s → GeometricallyIntegral s →
      topologicalKrullDim X=1 →
      Function.Bijective (StructureSheafCohomology.qToGlobal X s) →
      FiniteDimensional ℚ (StructureSheafCohomology.H1 X s) →
      2≤Module.finrank ℚ (StructureSheafCohomology.H1 X s) →
      Finite {p : StructureSheafCohomology.Base⟶X //
        p≫s=𝟙 StructureSheafCohomology.Base}

namespace FaltingsProperCurve
noncomputable section

/-- Rational scheme points, including the over-base equation. -/
abbrev RationalPointsOver (X : Scheme.{0}) (s : X⟶StructureSheafCohomology.Base) :=
  {p : StructureSheafCohomology.Base⟶X // p≫s=𝟙 StructureSheafCohomology.Base}

/-- Apply the published theorem. -/
theorem finite_rational_points (hF : FaltingsProperCurveTheorem)
    (X : Scheme.{0}) (s : X⟶StructureSheafCohomology.Base)
    (hp : IsProper s) (hs : Smooth s) (hi : GeometricallyIntegral s)
    (hd : topologicalKrullDim X=1)
    (hc : Function.Bijective (StructureSheafCohomology.qToGlobal X s))
    (hfd : FiniteDimensional ℚ (StructureSheafCohomology.H1 X s))
    (hg : 2≤Module.finrank ℚ (StructureSheafCohomology.H1 X s)) :
    Finite (RationalPointsOver X s) := hF X s hp hs hi hd hc hfd hg

/-- A separately proved exact finite cohomology dimension can supply the
genus lower bound; the integer is arbitrary and is not a cover-specific input. -/
theorem finite_of_finrank_eq (hF : FaltingsProperCurveTheorem)
    (X : Scheme.{0}) (s : X⟶StructureSheafCohomology.Base)
    (hp : IsProper s) (hs : Smooth s) (hi : GeometricallyIntegral s)
    (hd : topologicalKrullDim X=1)
    (hc : Function.Bijective (StructureSheafCohomology.qToGlobal X s))
    (hfd : FiniteDimensional ℚ (StructureSheafCohomology.H1 X s))
    (g : ℕ) (heq : Module.finrank ℚ (StructureSheafCohomology.H1 X s)=g) (hg : 2≤g) :
    Finite (RationalPointsOver X s) :=
  finite_rational_points hF X s hp hs hi hd hc hfd (heq ▸ hg)

end
end FaltingsProperCurve
end Z2Z4Rank6
