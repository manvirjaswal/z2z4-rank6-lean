import Z2Z4Rank6.SecondBaseJacobian
import Z2Z4Rank6.SecondJacobianExactRank
import Z2Z4Rank6.SecondJacobianTorsion
import Z2Z4Rank6.PrintedModelConductors
import Common.Elliptic.JacobianArithmetic

/-!
# Complete Theorem 8.1(a)

Jaswal, DOI 10.5281/zenodo.23437117. The projective two-quadric
base has genus one and infinitely many rational points. The
Jacobian is characterized by its Albanese universal property;
rank and torsion concern its abelian-variety rational sections.
The group-scheme/Mathlib point compatibility is proved using the
regular group law and rigidity. The conductor uses geometric
components of minimal regular proper fibers.
-/
namespace Z2Z4Rank6.SecondBaseJacobianArithmetic
noncomputable section
open AlgebraicGeometry CategoryTheory Jacobian
open Common.Elliptic.GeometricConductor Common.Elliptic.MulhollandModelTheorems

theorem theorem_8_1_a
    (hGenus : QuadricIntersectionModel.CFSTheorem28ii)
    (hJacobian : QuadricIntersectionModel.CFSTheorem28iii)
    (hCubic : GenusOneModelTheorem.CFSTheorem28iiDegreeOne)
    (hGroup : WeierstrassScheme.MilneRegularGroupLaw) (hRigidity : MilneCorollary22)
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hTorsionIntegral : OddPrimeTorsionIntegrality)
    (hModels : EllipticMinimalModelsTheorem) (h21 : Theorem21Components)
    (hOdd : Theorems23And24SemistableComponents) :
    RationalCurveGenus.IsSmoothProperGenusOne
      SecondBaseProjectiveScheme.scheme SecondBaseProjectiveScheme.structureMap ∧
    Infinite SecondBaseProjectiveRationalPoints.RationalPoint ∧
    PrintedModelConductorData.conductor hModels 2=182747931661680 ∧
    ∃ P : Presentation (Over.mk SecondBaseProjectiveScheme.structureMap)
        (Over.mk (WeierstrassScheme.structureMap J2)),
      Module.rank ℤ P.abelian.Points=2 ∧
      Nonempty (AddCommGroup.torsion P.abelian.Points ≃+ (ZMod 2 × ZMod 4)) := by
  obtain ⟨P⟩ := SecondBaseJacobian.J2_isJacobian hJacobian
  obtain ⟨L⟩ := hGroup J2
  exact ⟨SecondBaseProjectiveScheme.genus_one hGenus,
    SecondBaseProjectiveRationalPoints.rationalPoints_infinite hTorsionIntegral,
    PrintedModelConductors.j2_conductor hModels h21 hOdd,P,
    L.jacobian_rank_eq hCubic hRigidity P 2 (secondJacobian_rank_eq_two hMW hMazur hDescent),
    L.jacobian_torsion hCubic hRigidity P (secondJacobian_torsion_exact hMazur)⟩

end
end Z2Z4Rank6.SecondBaseJacobianArithmetic
