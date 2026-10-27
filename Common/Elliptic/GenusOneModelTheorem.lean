import Common.AlgebraicGeometry.CurveGenus
import Common.Elliptic.BinaryQuarticModel
import Common.Elliptic.WeierstrassScheme

/-!
# Published nonsingularity criteria for genus-one models

Source: Cremona–Fisher–Stoll, Minimisation and reduction of
2-, 3- and 4-coverings of elliptic curves, Algebra & Number Theory 4 (2010),
763–820, Theorem 2.8(ii); arXiv:0908.1741v1, p. 6. These are its degree-one
and degree-two, characteristic-zero specializations. The models are
homogeneous quotient Proj schemes; genus one is expanded through H1.

The converse from a smooth genus-one curve to nonzero discriminant is retained
to match the published if-and-only-if statement. The degree-two statement
specializes the generalized binary quartic to P=0, as in Definition 2.2.
-/

namespace GenusOneModelTheorem
open AlgebraicGeometry RationalCurveGenus

def CFSTheorem28iiDegreeOne : Prop :=
  ∀ W : WeierstrassCurve ℚ,
    IsSmoothProperGenusOne (WeierstrassScheme.scheme W) (WeierstrassScheme.structureMap W) ↔
      W.Δ ≠ 0

def CFSTheorem28iiDegreeTwo : Prop :=
  ∀ f : BinaryQuarticModel.BinaryQuartic ℚ,
    IsSmoothProperGenusOne (BinaryQuarticModel.scheme f) (BinaryQuarticModel.structureMap f) ↔
      BinaryQuarticModel.discriminant f ≠ 0

theorem weierstrass_genus_one (h : CFSTheorem28iiDegreeOne) (W : WeierstrassCurve ℚ)
    (hW : W.Δ ≠ 0) :
    IsSmoothProperGenusOne (WeierstrassScheme.scheme W) (WeierstrassScheme.structureMap W) :=
  (h W).mpr hW

theorem binaryQuartic_genus_one (h : CFSTheorem28iiDegreeTwo)
    (f : BinaryQuarticModel.BinaryQuartic ℚ) (hf : BinaryQuarticModel.discriminant f ≠ 0) :
    IsSmoothProperGenusOne (BinaryQuarticModel.scheme f) (BinaryQuarticModel.structureMap f) :=
  (h f).mpr hf

end GenusOneModelTheorem
