module

public import Z2Z4Rank6.ThirdTwistCoverAffine

@[expose] public section

/-! Third-twist base infinity charts, with U=u/t,V=v/t,W=w/t. -/
namespace Z2Z4Rank6.ThirdTwistCoverInfinity
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := ThirdTwistCoverPolynomialData.infinityRadicand
abbrev relation  := TripleSquareCover.relation (radicand)
abbrev definingIdeal  := TripleSquareCover.definingIdeal (radicand)
abbrev CoordinateRing  := TripleSquareCover.CoordinateRing (radicand)
abbrev z  : CoordinateRing := TripleSquareCover.parameter (radicand)
abbrev U  : CoordinateRing := TripleSquareCover.root (radicand) 0
abbrev V  : CoordinateRing := TripleSquareCover.root (radicand) 1
abbrev R  : CoordinateRing := TripleSquareCover.root (radicand) 2
abbrev W := R
abbrev scheme  : Scheme := Spec (CommRingCat.of (CoordinateRing))
def structureMap  : scheme⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing)))

theorem root_sq  (i : Fin 3) :
    (TripleSquareCover.root (radicand) i)^2=Polynomial.aeval (z) (radicand i) :=
  TripleSquareCover.root_sq _ _
end
end Z2Z4Rank6.ThirdTwistCoverInfinity
