module

public import Z2Z4Rank6.TripleSquareCover
public import Z2Z4Rank6.ThirdTwistCoverPolynomialData
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

/-! Third-twist base affine charts. All objects are
four-variable quotients by the three square relations. -/
namespace Z2Z4Rank6.ThirdTwistCoverAffine
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := ThirdTwistCoverPolynomialData.affineRadicand
abbrev relation  := TripleSquareCover.relation (radicand)
abbrev definingIdeal  := TripleSquareCover.definingIdeal (radicand)
abbrev CoordinateRing  := TripleSquareCover.CoordinateRing (radicand)
abbrev m  : CoordinateRing := TripleSquareCover.parameter (radicand)
abbrev t  := m
abbrev u  : CoordinateRing := TripleSquareCover.root (radicand) 0
abbrev v  : CoordinateRing := TripleSquareCover.root (radicand) 1
abbrev r  : CoordinateRing := TripleSquareCover.root (radicand) 2
abbrev w := r
abbrev scheme  : Scheme := Spec (CommRingCat.of (CoordinateRing))
def structureMap  : scheme⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing)))

theorem root_sq  (i : Fin 3) :
    (TripleSquareCover.root (radicand) i)^2=Polynomial.aeval (m) (radicand i) :=
  TripleSquareCover.root_sq _ _
end
end Z2Z4Rank6.ThirdTwistCoverAffine
