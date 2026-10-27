module

public import Z2Z4Rank6.GTorsionCoverAffine

@[expose] public section

/-! Signed G torsion-cover infinity charts, with U=u/t² and R=r/t⁴. -/
namespace Z2Z4Rank6.GTorsionCoverInfinity
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := GTorsionCoverPolynomialData.infinityRadicand
abbrev relation (ε : Bool) := DoubleSquareCover.relation (radicand ε)
abbrev definingIdeal (ε : Bool) := DoubleSquareCover.definingIdeal (radicand ε)
abbrev CoordinateRing (ε : Bool) := DoubleSquareCover.CoordinateRing (radicand ε)
abbrev z (ε : Bool) : CoordinateRing ε := DoubleSquareCover.parameter (radicand ε)
abbrev U (ε : Bool) : CoordinateRing ε := DoubleSquareCover.root (radicand ε) 0
abbrev R (ε : Bool) : CoordinateRing ε := DoubleSquareCover.root (radicand ε) 1
abbrev scheme (ε : Bool) : Scheme := Spec (CommRingCat.of (CoordinateRing ε))
def structureMap (ε : Bool) : scheme ε⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing ε)))

theorem root_sq (ε : Bool) (i : Fin 2) :
    (DoubleSquareCover.root (radicand ε) i)^2=Polynomial.aeval (z ε) (radicand ε i) :=
  DoubleSquareCover.root_sq _ _
end
end Z2Z4Rank6.GTorsionCoverInfinity
