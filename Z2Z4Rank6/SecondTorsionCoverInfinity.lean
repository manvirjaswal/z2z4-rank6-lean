import Z2Z4Rank6.SecondTorsionCoverAffine

/-! Signed second torsion-cover infinity charts, with R=r/t^2. -/
namespace Z2Z4Rank6.SecondTorsionCoverInfinity
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := SecondTorsionCoverPolynomialData.infinityRadicand
abbrev relation (ε : Bool) := TripleSquareCover.relation (radicand ε)
abbrev definingIdeal (ε : Bool) := TripleSquareCover.definingIdeal (radicand ε)
abbrev CoordinateRing (ε : Bool) := TripleSquareCover.CoordinateRing (radicand ε)
abbrev z (ε : Bool) : CoordinateRing ε := TripleSquareCover.parameter (radicand ε)
abbrev U (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 0
abbrev V (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 1
abbrev R (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 2
abbrev scheme (ε : Bool) : Scheme := Spec (CommRingCat.of (CoordinateRing ε))
def structureMap (ε : Bool) : scheme ε⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing ε)))

theorem root_sq (ε : Bool) (i : Fin 3) :
    (TripleSquareCover.root (radicand ε) i)^2=Polynomial.aeval (z ε) (radicand ε i) :=
  TripleSquareCover.root_sq _ _
end
end Z2Z4Rank6.SecondTorsionCoverInfinity
