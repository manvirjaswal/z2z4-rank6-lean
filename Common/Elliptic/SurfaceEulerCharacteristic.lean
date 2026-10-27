module

public import Common.Elliptic.ComplexEllipticSurfaceTheorems
public import Common.AlgebraicGeometry.ProjectiveScheme

@[expose] public section

/-!
# Euler sum on projective elliptic surfaces with a singular fiber

Schuett–Shioda, Elliptic Surfaces, arXiv:0907.0298v3, Theorem 6.10 p. 27.
The source's standing singular-fiber condition is retained. The input
is restricted to surfaces with a multiplicative fiber, expressed
by a Neron-polygon isomorphism with positive component count.
This is a stronger hypothesis and is verified in the concrete application.
All Euler numbers refer to rational singular homology.
-/
namespace Common.Elliptic.SurfaceEulerCharacteristic
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory
open SurfaceModel ComplexEllipticSurfaceTheorems
open Common.AlgebraicGeometry

def HasMultiplicativeFiber {W : WeierstrassCurve (RatFunc ℂ)} (M : RegularModel ℂ W) : Prop :=
  ∃ (t : Option ℂ) (n : ℕ),0<n ∧ NeronPolygon.IsTypeI ℂ (fiberOver M t) n

/-- Theorem 6.10, char 0 and a multiplicative singular fiber. The
finite set may include good fibers, whose Euler number is zero. -/
def SchuttShiodaTheorem610 : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W),
    M.IsRelativelyMinimal → M.HasSection →
    ProjectiveScheme.IsProjective ℂ M.scheme M.structureMap → HasMultiplicativeFiber M →
    ∀ S : Finset (Option ℂ),(∀ t∉S,IsGoodFiber (fiberOver M t)) →
      ComplexPointsTopology.HasFiniteHomology ℂ M.scheme M.structureMap 4 ∧
      ComplexPointsTopology.euler ℂ M.scheme M.structureMap 4=
        ∑ t∈S,ComplexPointsTopology.euler ℂ (fiberOver M t).left (fiberOver M t).hom 2

end
end Common.Elliptic.SurfaceEulerCharacteristic
