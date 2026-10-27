import Z2Z4Rank6.StructureSheafCohomology
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Smooth proper schemes with no extra global constants

Stacks Lemma 33.25.4 (tag 056T) makes a smooth scheme over a field
geometrically normal. Lemma 33.10.7 (tag 0FD3) then identifies canonical
global sections equal to the ground field with geometric integrality,
for a proper geometrically normal scheme.

The proposition below is this direct corollary over Q.
It uses schemes, the structure map, its map on
global sections, and Mathlib's geometric-integrality property.

-/
namespace Z2Z4Rank6
open AlgebraicGeometry CategoryTheory

/-- Published smooth-proper global-constants criterion. The conclusion
asserts integrality of the geometric field base changes. -/
def SmoothProperGlobalConstantsGeometricIntegralityTheorem : Prop :=
  ∀ (X : Scheme.{0}) (s : X ⟶ StructureSheafCohomology.Base),
    IsProper s → Smooth s →
      Function.Bijective (StructureSheafCohomology.qToGlobal X s) →
        GeometricallyIntegral s

namespace SmoothProperGeometricIntegrality

/-- Apply the published criterion. -/
theorem geometricallyIntegral_of_global_constants
    (h : SmoothProperGlobalConstantsGeometricIntegralityTheorem)
    (X : Scheme.{0}) (s : X ⟶ StructureSheafCohomology.Base)
    (hproper : IsProper s) (hsmooth : Smooth s)
    (hconstants : Function.Bijective (StructureSheafCohomology.qToGlobal X s)) :
    GeometricallyIntegral s :=
  h X s hproper hsmooth hconstants

end SmoothProperGeometricIntegrality
end Z2Z4Rank6
