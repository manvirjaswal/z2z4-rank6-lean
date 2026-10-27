import Z2Z4Rank6.SurfaceRationalDescent

/-!
# Complete geometric statement of Lemma 3.1(b)

The printed discriminant has the printed factors;
there is a rational minimal regular K3 model of the printed
Q(n) cubic. Its complex extension is a minimal K3 model, with
four I4, three I2 and two I1 fibers at exactly the printed geometric
parameters. The fiber Euler numbers sum to 24, and the
total singular-homology Euler number is 24. All other linear
complex base points have good fibers.
-/
namespace Z2Z4Rank6.EllipticSurfaceStatements
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open Common.Elliptic.SurfaceModel Common.Elliptic.SurfaceDescentSources
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open Common.AlgebraicGeometry.K3BaseChange
open SurfaceBadParameters SurfaceWeierstrassCharts
set_option backward.isDefEq.respectTransparency false

/-- The printed discriminant, including its nonzero scalar. -/
def DiscriminantStatement : Prop :=
  SurfaceRationalData.finiteEquation.Δ=
    16*(surfaceW Polynomial.X)^4*((surfaceS Polynomial.X)^2-4*(surfaceW Polynomial.X)^2) ∧
  SurfaceRationalData.finiteEquation.Δ=C (deltaConstant (R:=ℚ)) *
    (Polynomial.X-1)^4*(Polynomial.X-81)^4*(Polynomial.X-121)^4*(Polynomial.X-9801)^4*
      Polynomial.X*(Polynomial.X-99)^2*((Polynomial.X^2-2*Polynomial.X+9801))^2 ∧
  deltaConstant (R:=ℚ)≠0

/-- Every numerical geometric invariant here is attached to a
scheme or singular-homology group. -/
def GeometryStatement : Prop :=
  ∃ M : SurfaceRationalDescent.Model,M.IsRelativelyMinimal ∧ M.HasSection ∧
    Common.AlgebraicGeometry.IsK3 ℚ M.scheme M.structureMap ∧
    ∃ MC : SurfaceComplexGeometry.Model,MC.IsRelativelyMinimal ∧ MC.HasSection ∧
      Common.AlgebraicGeometry.IsK3 ℂ MC.scheme MC.structureMap ∧
      (∃ p : MC.scheme ⟶ M.scheme,
        IsPullback p MC.structureMap M.structureMap (extensionMap ℚ ℂ)) ∧
      ComplexPointsTopology.HasFiniteHomology ℂ MC.scheme MC.structureMap 4 ∧
      ComplexPointsTopology.euler ℂ MC.scheme MC.structureMap 4=24 ∧
      (∀ i : Fin 9,Common.Elliptic.NeronPolygon.IsTypeI ℂ
        (fiberOver MC (parameter i)) (order i) ∧
        ComplexPointsTopology.HasFiniteHomology ℂ
          (fiberOver MC (parameter i)).left (fiberOver MC (parameter i)).hom 2 ∧
        ComplexPointsTopology.euler ℂ
          (fiberOver MC (parameter i)).left (fiberOver MC (parameter i)).hom 2=(order i : ℤ)) ∧
      (∑ i : Fin 9,ComplexPointsTopology.euler ℂ
        (fiberOver MC (parameter i)).left (fiberOver MC (parameter i)).hom 2)=24 ∧
      (∀ p : Spec (CommRingCat.of ℂ) ⟶ ProjectiveLine.scheme ℂ,
        p≫ProjectiveLine.structureMap ℂ=𝟙 _ →
        (∃ i : Fin 9,p=parameterPoint (parameter i) ∧
          Common.Elliptic.NeronPolygon.IsTypeI ℂ (SurfaceComplexGeometry.fiberAt MC p) (order i)) ∨
          IsGoodFiber (SurfaceComplexGeometry.fiberAt MC p))

theorem discriminant_statement : DiscriminantStatement := by
  refine ⟨affine_delta (R:=ℚ),?_,?_⟩
  · simpa [twistN] using affine_delta_factorization (R:=ℚ)
  · norm_num [deltaConstant]


end
end Z2Z4Rank6.EllipticSurfaceStatements
