module

public import Common.Elliptic.BinaryQuarticModel
public import Common.Elliptic.WeierstrassScheme
public import Common.AlgebraicGeometry.Jacobian

@[expose] public section

/-!
# The Jacobian of a binary quartic

The explicit published theorem argument is the degree-two, rational-field
specialization of Cremona–Fisher–Stoll, *Minimisation and reduction of
2-, 3- and 4-coverings of elliptic curves*, Algebra & Number Theory 4
(2010), 763–820, Theorem 2.8(iii); arXiv:0908.1741v1, p. 6.
The invariant conventions are Definition 2.2, p. 4: c4=16I, c6=32J.

Both curves are homogeneous quotient Proj schemes. The conclusion
is the full basepoint-free Albanese universal property among
abelian varieties, with an over-Q scheme isomorphism to the
displayed invariant cubic. No rational point on the quartic is required.
The formula is -27c4 and -54c6, before any coordinate scaling.
-/

namespace BinaryQuarticModel
noncomputable section
open AlgebraicGeometry CategoryTheory

/-- The exact short Weierstrass equation in CFS Theorem 2.8(iii). -/
def invariantCurve (f : BinaryQuartic ℚ) : WeierstrassCurve ℚ :=
  ⟨0, 0, 0, -27 * c4 f, -54 * c6 f⟩

theorem invariantCurve_discriminant (f : BinaryQuartic ℚ) :
    (invariantCurve f).Δ = 6 ^ 12 * discriminant f := by
  simp only [invariantCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, discriminant]
  ring

/-- The published CFS theorem, specialized only to rational
binary quartics. -/
def CFSBinaryQuarticJacobianTheorem : Prop :=
  ∀ f : BinaryQuartic ℚ, discriminant f ≠ 0 →
    Jacobian.IsJacobian (Over.mk (structureMap f))
      (Over.mk (WeierstrassScheme.structureMap (invariantCurve f)))

theorem jacobian_invariantCurve (h : CFSBinaryQuarticJacobianTheorem)
    (f : BinaryQuartic ℚ) (hdisc : discriminant f ≠ 0) :
    Jacobian.IsJacobian (Over.mk (structureMap f))
      (Over.mk (WeierstrassScheme.structureMap (invariantCurve f))) := h f hdisc

/-- Transport the invariant cubic along a proved over-Q scheme
isomorphism; coefficient identities alone cannot instantiate this theorem. -/
theorem jacobian_of_invariantCurve_iso (h : CFSBinaryQuarticJacobianTheorem)
    (f : BinaryQuartic ℚ) (hdisc : discriminant f ≠ 0)
    (J : Scheme.{0}) (sJ : J ⟶ Spec (CommRingCat.of ℚ))
    (e : Over.mk sJ ≅ Over.mk (WeierstrassScheme.structureMap (invariantCurve f))) :
    Jacobian.IsJacobian (Over.mk (structureMap f)) (Over.mk sJ) :=
  Jacobian.isJacobian_targetIso e (h f hdisc)

end
end BinaryQuarticModel
