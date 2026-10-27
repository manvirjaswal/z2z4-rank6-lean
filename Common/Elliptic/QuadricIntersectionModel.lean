import Common.AlgebraicGeometry.HomogeneousQuotient
import Common.AlgebraicGeometry.CurveGenus
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Models given by two quadrics

The scheme attached to a pair of homogeneous quadrics is its Proj,
with the usual grading. Its invariants are computed from the determinant
of the pencil of Hessian matrices.

References: J. E. Cremona, T. A. Fisher and M. Stoll, *Minimisation and
reduction of 2-, 3- and 4-coverings of elliptic curves*, Algebra & Number
Theory 4 (2010), 763–820, Definition 2.4 and Theorem 2.8(ii). The author
manuscript arXiv:0908.1741v1, pp. 5–6, gives the conventions used here:
c4=2⁻⁴c4(det(xA+zB)), c6=2⁻⁶c6(det(xA+zB)).
-/

namespace QuadricIntersectionModel
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
open scoped Classical

abbrev PolynomialRing := MvPolynomial (Fin 4) ℚ

/-- An ordered pair of homogeneous quadratic polynomials. -/
structure Model where
  polynomial : Fin 2 → PolynomialRing
  homogeneous : ∀ i, (polynomial i).IsHomogeneous 2

def polynomialGrading : ℕ → Submodule ℚ PolynomialRing :=
  MvPolynomial.homogeneousSubmodule (Fin 4) ℚ

instance polynomialGradedAlgebra : GradedAlgebra polynomialGrading :=
  MvPolynomial.gradedAlgebra

def definingIdeal (q : Model) : Ideal PolynomialRing :=
  Ideal.span (Set.range q.polynomial)

theorem definingIdeal_homogeneous (q : Model) :
    (definingIdeal q).IsHomogeneous polynomialGrading :=
  Ideal.homogeneous_span polynomialGrading _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨2, q.homogeneous i⟩)

abbrev CoordinateRing (q : Model) := PolynomialRing ⧸ definingIdeal q

def grading (q : Model) : ℕ → Submodule ℚ (CoordinateRing q) :=
  HomogeneousQuotient.component polynomialGrading (definingIdeal q)

instance coordinateRingGradedAlgebra (q : Model) : GradedAlgebra (grading q) :=
  HomogeneousQuotient.quotientGradedAlgebra polynomialGrading (definingIdeal q)
    (definingIdeal_homogeneous q)

/-- The projective intersection of the two quadrics. -/
def scheme (q : Model) : Scheme := Proj (grading q)

def structureMap (q : Model) : scheme q ⟶ Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero (grading q) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading q 0)))

/-- Hessians of the quadratic forms, with their second derivatives. -/
def hessian (q : Model) (k : Fin 2) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => (MvPolynomial.pderiv i (MvPolynomial.pderiv j (q.polynomial k))).coeff 0

/-- Dehomogenize det(xA+zB) at z=1; its coefficients retain the binary
quartic's possible root at infinity. -/
def pencilPolynomial (q : Model) : Polynomial ℚ :=
  Matrix.det (fun i j => Polynomial.C (hessian q 0 i j) * Polynomial.X +
    Polynomial.C (hessian q 1 i j))

def invariantI (q : Model) : ℚ :=
  let f := pencilPolynomial q
  12 * f.coeff 4 * f.coeff 0 - 3 * f.coeff 3 * f.coeff 1 + (f.coeff 2)^2

def invariantJ (q : Model) : ℚ :=
  let f := pencilPolynomial q
  72 * f.coeff 4 * f.coeff 2 * f.coeff 0 +
    9 * f.coeff 3 * f.coeff 2 * f.coeff 1 -
    27 * f.coeff 4 * (f.coeff 1)^2 - 27 * (f.coeff 3)^2 * f.coeff 0 -
    2 * (f.coeff 2)^3

def c4 (q : Model) : ℚ := invariantI q
def c6 (q : Model) : ℚ := invariantJ q / 2
def discriminant (q : Model) : ℚ := ((c4 q)^3 - (c6 q)^2) / 1728

/-- Cremona–Fisher–Stoll, Theorem 2.8(ii), arXiv:0908.1741v1 p. 6:
a degree-four genus-one model is nonsingular exactly when its discriminant
is nonzero. Here the conclusion expands the standard meaning into
scheme smoothness, properness, geometric integrality and genus one. -/
def CFSTheorem28ii : Prop :=
  ∀ q : Model,
    AlgebraicGeometry.RationalCurveGenus.IsSmoothProperGenusOne
      (scheme q) (structureMap q) ↔ discriminant q ≠ 0

theorem genus_one (h : CFSTheorem28ii) (q : Model) (hq : discriminant q ≠ 0) :
    AlgebraicGeometry.RationalCurveGenus.IsSmoothProperGenusOne
      (scheme q) (structureMap q) := (h q).mpr hq

end
end QuadricIntersectionModel
