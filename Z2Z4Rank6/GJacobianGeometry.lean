module

public import Z2Z4Rank6.GProjectiveJacobian
public import Z2Z4Rank6.GJacobianExactRank
public import Z2Z4Rank6.GJacobianTorsion
public import Z2Z4Rank6.PrintedModelConductors
public import Common.Elliptic.JacobianArithmetic

@[expose] public section

/-!
# Complete Proposition 7.2(a)

Jaswal, DOI 10.5281/zenodo.23437117. The base is the complete
weighted projective quartic, and its Jacobian satisfies the
Albanese universal property. Its rank and torsion below belong to that
abelian variety's rational-section group. Their identification
with Mathlib's printed Weierstrass point group comes from a
group-scheme isomorphism. The conductor uses minimal regular
proper fibers.
-/
namespace Z2Z4Rank6.GJacobianGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory Jacobian
open Common.Elliptic.GeometricConductor Common.Elliptic.MulhollandModelTheorems

theorem proposition_7_2_a
    (hGenus : GenusOneModelTheorem.CFSTheorem28iiDegreeTwo)
    (hJacobian : BinaryQuarticModel.CFSBinaryQuarticJacobianTheorem)
    (hCubic : GenusOneModelTheorem.CFSTheorem28iiDegreeOne)
    (hGroup : WeierstrassScheme.MilneRegularGroupLaw) (hRigidity : MilneCorollary22)
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOdd : Theorems23And24SemistableComponents) :
    RationalCurveGenus.IsSmoothProperGenusOne
      GProjectiveQuartic.scheme GProjectiveQuartic.structureMap ∧
    Nonempty {p : Spec (CommRingCat.of ℚ) ⟶ GProjectiveQuartic.scheme //
      p≫GProjectiveQuartic.structureMap=𝟙 (Spec (CommRingCat.of ℚ))} ∧
    PrintedModelConductorData.conductor hModels 1=683760 ∧
    ∃ P : Presentation (Over.mk GProjectiveQuartic.structureMap)
        (Over.mk (WeierstrassScheme.structureMap JG)),
      Module.rank ℤ P.abelian.Points=2 ∧
      Nonempty (AddCommGroup.torsion P.abelian.Points ≃+ (ZMod 2 × ZMod 4)) := by
  obtain ⟨P⟩ := GProjectiveJacobian.jg_isJacobian hJacobian
  obtain ⟨L⟩ := hGroup JG
  exact ⟨GProjectiveQuartic.genus_one hGenus,GProjectiveQuartic.rational_point_exists,
    PrintedModelConductors.jg_conductor hModels h21 hOdd,P,
    L.jacobian_rank_eq hCubic hRigidity P 2 (gJacobian_rank_eq_two hMW hMazur hDescent),
    L.jacobian_torsion hCubic hRigidity P (gJacobian_torsion_exact hMazur)⟩

end
end Z2Z4Rank6.GJacobianGeometry
