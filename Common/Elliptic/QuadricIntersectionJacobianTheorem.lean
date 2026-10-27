module

public import Common.Elliptic.QuadricIntersectionModel
public import Common.Elliptic.WeierstrassScheme
public import Common.AlgebraicGeometry.Jacobian

@[expose] public section

/-!
# Jacobians of quadric intersections

Cremona–Fisher–Stoll, *Minimisation and reduction of 2-, 3- and
4-coverings of elliptic curves*, Algebra & Number Theory 4 (2010), 763–820,
Theorem 2.8(iii); arXiv:0908.1741v1 p. 6. The projective intersection's
Jacobian has equation y²=x³−27c4x−54c6 when Δ≠0 in characteristic zero.
The Jacobian predicate is its universal property among abelian
group schemes.
-/

namespace QuadricIntersectionModel
noncomputable section
open AlgebraicGeometry CategoryTheory

def invariantCurve (q : Model) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -27*c4 q
  a₆ := -54*c6 q

theorem invariantCurve_discriminant (q : Model) :
    (invariantCurve q).Δ=6^12*discriminant q := by
  simp only [invariantCurve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈,discriminant]
  ring

/-- CFS Theorem 2.8(iii), p. 6, specialized to degree-four models over Q.
The invariant-ring assertion in the first sentence is not needed here;
the complete Jacobian-equation conclusion is retained. -/
def CFSTheorem28iii : Prop :=
  ∀ q : Model, discriminant q≠0 →
    AlgebraicGeometry.Jacobian.IsJacobian
      (Over.mk (structureMap q))
      (Over.mk (WeierstrassScheme.structureMap (invariantCurve q)))

theorem invariantCurve_isJacobian (h : CFSTheorem28iii) (q : Model)
    (hq : discriminant q≠0) :
    AlgebraicGeometry.Jacobian.IsJacobian
      (Over.mk (structureMap q))
      (Over.mk (WeierstrassScheme.structureMap (invariantCurve q))) := h q hq

end
end QuadricIntersectionModel
