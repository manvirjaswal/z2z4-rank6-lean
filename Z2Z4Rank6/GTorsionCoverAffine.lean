import Z2Z4Rank6.DoubleSquareCover
import Z2Z4Rank6.GTorsionCoverPolynomialData
import Mathlib.AlgebraicGeometry.AffineScheme

/-! Signed G torsion-cover affine charts. All objects are
three-variable quotients by the two square relations. -/
namespace Z2Z4Rank6.GTorsionCoverAffine
noncomputable section
open AlgebraicGeometry CategoryTheory
abbrev radicand := GTorsionCoverPolynomialData.affineRadicand
abbrev relation (ε : Bool) := DoubleSquareCover.relation (radicand ε)
abbrev definingIdeal (ε : Bool) := DoubleSquareCover.definingIdeal (radicand ε)
abbrev CoordinateRing (ε : Bool) := DoubleSquareCover.CoordinateRing (radicand ε)
abbrev m (ε : Bool) : CoordinateRing ε := DoubleSquareCover.parameter (radicand ε)
abbrev t (ε : Bool) := m ε
abbrev u (ε : Bool) : CoordinateRing ε := DoubleSquareCover.root (radicand ε) 0
abbrev r (ε : Bool) : CoordinateRing ε := DoubleSquareCover.root (radicand ε) 1
abbrev scheme (ε : Bool) : Scheme := Spec (CommRingCat.of (CoordinateRing ε))
def structureMap (ε : Bool) : scheme ε⟶Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ (CoordinateRing ε)))

theorem root_sq (ε : Bool) (i : Fin 2) :
    (DoubleSquareCover.root (radicand ε) i)^2=Polynomial.aeval (m ε) (radicand ε i) :=
  DoubleSquareCover.root_sq _ _
end
end Z2Z4Rank6.GTorsionCoverAffine
