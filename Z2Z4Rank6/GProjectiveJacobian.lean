import Z2Z4Rank6.GJacobianInvariants
import Z2Z4Rank6.GProjectivePoint
import Common.Elliptic.WeierstrassSchemeVariableChange

/-!
# The Jacobian scheme of G

Jaswal, Proposition 7.2(a), DOI 10.5281/zenodo.23437117. CFS Theorem 2.8(iii), arXiv:0908.1741v1 p.
6, gives the invariant Jacobian.
The coefficient change to the printed model and the induced
over-Q scheme isomorphism are both proved. The Jacobian is characterized
by its full basepoint-free Albanese universal property among abelian
variety group schemes.

The abstract group's rational-point identification with Mathlib's printed
Weierstrass point group is a separate bridge; numerical rank and torsion
are not asserted by an underlying scheme isomorphism alone.
-/

namespace Z2Z4Rank6.GProjectiveJacobian
noncomputable section
open AlgebraicGeometry CategoryTheory BinaryQuarticModel

def invariantOverIso :
    Over.mk (WeierstrassScheme.structureMap JG) ≅
      Over.mk (WeierstrassScheme.structureMap (invariantCurve GProjectiveQuartic.model)) := by
  let e := WeierstrassScheme.VariableChange.overBaseIso
    (invariantCurve GProjectiveQuartic.model) GJacobianInvariants.modelChange
  have h : Over.mk (WeierstrassScheme.structureMap
      (GJacobianInvariants.modelChange • invariantCurve GProjectiveQuartic.model)) ≅
      Over.mk (WeierstrassScheme.structureMap (invariantCurve GProjectiveQuartic.model)) :=
    Over.isoMk e.val e.property
  exact eqToIso (congrArg
    (fun W : WeierstrassCurve ℚ => Over.mk (WeierstrassScheme.structureMap W))
    GJacobianInvariants.variableChange_eq.symm) ≪≫ h

theorem jg_isJacobian (hCFS : CFSBinaryQuarticJacobianTheorem) :
    Jacobian.IsJacobian (Over.mk GProjectiveQuartic.structureMap)
      (Over.mk (WeierstrassScheme.structureMap JG)) :=
  jacobian_of_invariantCurve_iso hCFS GProjectiveQuartic.model
    GProjectiveQuartic.discriminant_ne_zero
    (WeierstrassScheme.scheme JG) (WeierstrassScheme.structureMap JG) invariantOverIso

theorem proposition_7_2_a_geometry
    (hGenus : GenusOneModelTheorem.CFSTheorem28iiDegreeTwo)
    (hJacobian : CFSBinaryQuarticJacobianTheorem) :
    RationalCurveGenus.IsSmoothProperGenusOne
      GProjectiveQuartic.scheme GProjectiveQuartic.structureMap ∧
      Nonempty {p : Spec (CommRingCat.of ℚ) ⟶ GProjectiveQuartic.scheme //
        p ≫ GProjectiveQuartic.structureMap = 𝟙 (Spec (CommRingCat.of ℚ))} ∧
      Jacobian.IsJacobian (Over.mk GProjectiveQuartic.structureMap)
        (Over.mk (WeierstrassScheme.structureMap JG)) :=
  ⟨GProjectiveQuartic.genus_one hGenus,GProjectiveQuartic.rational_point_exists,
    jg_isJacobian hJacobian⟩

end
end Z2Z4Rank6.GProjectiveJacobian
