module

public import Z2Z4Rank6.SecondBaseProjectivePointEquiv
public import Z2Z4Rank6.SecondBaseJacobianInvariants

@[expose] public section

/-!
# Theorem 8.1(a): the second base has genus one and infinitely many points

The projective intersection uses only the invertible rational scaling
U=1089s2,V=1089s3 of the printed equations. Its smooth proper
geometrically integral genus-one statement uses generic CFS 2.8(ii); its
rational-point infinitude uses the already proved infinite-order
point and generic odd-prime torsion integrality. Every printed rational
G2 point and every over-Q scheme point correspond in both directions.
The separate Jacobian and conductor clauses are not asserted here.
-/

namespace Z2Z4Rank6.SecondBaseGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem theorem_8_1_a_geometry (hCFS : QuadricIntersectionModel.CFSTheorem28ii)
    (hOdd : OddPrimeTorsionIntegrality) :
    RationalCurveGenus.IsSmoothProperGenusOne
      SecondBaseProjectiveScheme.scheme SecondBaseProjectiveScheme.structureMap ∧
      Infinite SecondBaseProjectiveRationalPoints.RationalPoint ∧
      Nonempty SecondBaseProjectiveRationalPoints.RationalPoint :=
  ⟨SecondBaseProjectiveScheme.genus_one hCFS,
    SecondBaseProjectiveRationalPoints.rationalPoints_infinite hOdd,
    SecondBaseProjectiveRationalPoints.rationalPoint_nonempty⟩

def printedPointEquiv : SecondFamily.G2Point ℚ≃
    {p : Spec (CommRingCat.of ℚ) ⟶ SecondBaseProjectiveScheme.scheme //
      p≫SecondBaseProjectiveScheme.structureMap=𝟙 _} :=
  SecondBaseProjectivePointEquiv.rationalPointEquiv

end
end Z2Z4Rank6.SecondBaseGeometry
