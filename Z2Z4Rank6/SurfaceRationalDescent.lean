import Z2Z4Rank6.SurfaceRationalData
import Z2Z4Rank6.SurfaceComplexAllFibers
import Common.Elliptic.SurfaceBaseChangeRegularModel
import Common.Elliptic.SurfaceModelEquationTransport
import Common.AlgebraicGeometry.K3CartesianDescent
import Common.Elliptic.SurfaceDescentSources
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Rational K3 surface through the algebraic-constant tower

The rational model is extended first to the algebraic closure of Q
inside C, then to C. The first minimality step is Overkamp–Smeets
Proposition 2.6; the second is proved from negative-curve descent and
Castelnuovo. The total field-extension square is obtained by pullback pasting.
Relative minimality follows from these two field-extension steps.
-/
namespace Z2Z4Rank6.SurfaceRationalDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Common.Elliptic.SurfaceModel Common.Elliptic.SurfaceBaseChange
open Common.Elliptic.SurfaceWeierstrassData Common.Elliptic.SurfaceDescentSources
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open Common.AlgebraicGeometry.K3BaseChange
open SurfaceBadParameters
set_option backward.isDefEq.respectTransparency false

abbrev Constants := algebraicClosure ℚ ℂ

instance constants_isAlgClosed : IsAlgClosed Constants := IsAlgClosure.isAlgClosed ℚ

abbrev rationalCurve := SurfaceRationalData.curve
abbrev algebraicCurve := rationalCurve.map (constantExtension ℚ Constants)
abbrev Model := RegularModel ℚ SurfaceRationalData.curve

theorem curve_complex : algebraicCurve.map (constantExtension Constants ℂ)=SurfaceComplexData.curve :=
  (curve_constantExtension_comp ℚ Constants ℂ rationalCurve).trans SurfaceRationalData.curve_complex

def algebraicModel (H : PublishedInputs) (M : Model) : RegularModel Constants algebraicCurve :=
  regularModel ℚ Constants M (H.regular Constants) (H.negative_curve.dimension ℚ Constants)

def complexModel (H : PublishedInputs) (M : Model) : SurfaceComplexGeometry.Model :=
  (regularModel Constants ℂ (algebraicModel H M) (H.regular ℂ)
    (H.negative_curve.dimension Constants ℂ)).changeEquation curve_complex

def complexCoefficientMap (H : PublishedInputs) (M : Model) :
    (complexModel H M).scheme ⟶ M.scheme :=
  coefficientMap Constants ℂ (algebraicModel H M)≫coefficientMap ℚ Constants M

theorem complexModel_isPullback (H : PublishedInputs) (M : Model) :
    IsPullback (complexCoefficientMap H M) (complexModel H M).structureMap
      M.structureMap (extensionMap ℚ ℂ) := by
  have hp := (structure_isPullback Constants ℂ (algebraicModel H M)).paste_horiz
    (structure_isPullback ℚ Constants M)
  rw [extensionMap_comp ℚ Constants ℂ] at hp
  exact hp

theorem complexModel_hasSection (H : PublishedInputs) (M : Model) (hs : M.HasSection) :
    (complexModel H M).HasSection := by
  apply RegularModel.changeEquation_hasSection
  exact regularModel_hasSection Constants ℂ (algebraicModel H M) _ _
    (regularModel_hasSection ℚ Constants M _ _ hs)

theorem complexModel_isRelativelyMinimal (H : PublishedInputs) (M : Model)
    (hM : M.IsRelativelyMinimal) (hs : M.HasSection)
    (hProj : Common.AlgebraicGeometry.ProjectiveScheme.IsProjective ℚ M.scheme M.structureMap) :
    (complexModel H M).IsRelativelyMinimal := by
  have hMA : (algebraicModel H M).IsRelativelyMinimal :=
    H.algebraic_minimality ℚ Constants rationalCurve M hProj hs hM _ _
  have hProjA := H.projective_baseChange ℚ Constants M.scheme (algebraicModel H M).scheme
    M.structureMap (algebraicModel H M).structureMap (coefficientMap ℚ Constants M)
    (structure_isPullback ℚ Constants M) hProj
  have hProjC := H.projective_baseChange Constants ℂ (algebraicModel H M).scheme
    (scheme Constants ℂ (algebraicModel H M)) (algebraicModel H M).structureMap
    (structureMap Constants ℂ (algebraicModel H M))
    (coefficientMap Constants ℂ (algebraicModel H M))
    (structure_isPullback Constants ℂ (algebraicModel H M)) hProjA
  apply RegularModel.changeEquation_isRelativelyMinimal
  exact minimality_algebraically_closed Constants ℂ H.negative_curve H.line_bundle_descent
    (H.projective_line Constants) (H.projective_line_h1 ℂ)
    (H.castelnuovo Constants) (H.castelnuovo ℂ) (H.exceptional_conormal ℂ) (H.minimality ℂ)
    algebraicCurve (algebraicModel H M) hMA hProjA _ _ hProjC


end
end Z2Z4Rank6.SurfaceRationalDescent
