module

public import Z2Z4Rank6.TripleSquareCover
public import Z2Z4Rank6.SecondTorsionCoverPolynomialData
public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

/-! Signed second torsion-cover affine charts. All objects are
four-variable quotients by the three square relations. -/
namespace Z2Z4Rank6.SecondTorsionCoverAffine
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := SecondTorsionCoverPolynomialData.affineRadicand
abbrev relation (ε : Bool) := TripleSquareCover.relation (radicand ε)
abbrev definingIdeal (ε : Bool) := TripleSquareCover.definingIdeal (radicand ε)
abbrev CoordinateRing (ε : Bool) := TripleSquareCover.CoordinateRing (radicand ε)
abbrev m (ε : Bool) : CoordinateRing ε := TripleSquareCover.parameter (radicand ε)
abbrev t (ε : Bool) := m ε
abbrev u (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 0
abbrev v (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 1
abbrev r (ε : Bool) : CoordinateRing ε := TripleSquareCover.root (radicand ε) 2
abbrev scheme (ε : Bool) : Scheme := Spec (CommRingCat.of (CoordinateRing ε))
def structureMap (ε : Bool) : scheme ε⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing ε)))

theorem root_sq (ε : Bool) (i : Fin 3) :
    (TripleSquareCover.root (radicand ε) i)^2=Polynomial.aeval (m ε) (radicand ε i) :=
  TripleSquareCover.root_sq _ _
end
end Z2Z4Rank6.SecondTorsionCoverAffine
