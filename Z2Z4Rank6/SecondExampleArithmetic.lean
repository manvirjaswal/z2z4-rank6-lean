import Z2Z4Rank6.SecondExampleConductor
import Z2Z4Rank6.SecondReductionRank

/-!
# The printed fiber in Theorem 8.1(d), including its conductor

Jaswal, DOI 10.5281/zenodo.23437117. The over-Q complete cubics
are isomorphic. The six specialized points are independent in the
group and its torsion subgroup is exactly Z/2 x Z/4. The extra
squarefree conductor printed immediately after the theorem is included,
using the globally minimal integral equation and regular models.
-/
namespace Z2Z4Rank6.SecondExampleArithmetic
noncomputable section
open AlgebraicGeometry CategoryTheory WeierstrassCurve
open Common.Elliptic.GeometricConductor
open SecondFamily SecondReductionData

theorem rationalCurve_eq : rationalCurve=SecondExampleRankSeven.curve := by
  ext <;> norm_num [rationalCurve,SecondExampleRankSeven.curve,
    SecondExampleRankSeven.A,SecondExampleRankSeven.B,a0,b0,E]

def fiberOverIso :
    Over.mk (WeierstrassScheme.structureMap SecondExampleRankSeven.curve) ≅
      Over.mk (WeierstrassScheme.structureMap (F baseW)) := by
  let c := scalingChange (Units.mk0 scale (by norm_num [scale]))
  let e := WeierstrassScheme.VariableChange.overBaseIso (F baseW) c
  have h : Over.mk (WeierstrassScheme.structureMap (c • F baseW)) ≅
      Over.mk (WeierstrassScheme.structureMap (F baseW)) := Over.isoMk e.val e.property
  have hc : c • F baseW=SecondExampleRankSeven.curve :=
    fiber_variableChange.trans rationalCurve_eq
  exact eqToIso (congrArg (fun W : WeierstrassCurve ℚ=>
    Over.mk (WeierstrassScheme.structureMap W)) hc.symm) ≪≫ h

theorem theorem_8_1_d
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hModels : EllipticMinimalModelsTheorem) (hTate : CremonaTateSteps4And19to21) :
    basePoint.s1=23306521/20091929 ∧
    Nonempty (Over.mk (WeierstrassScheme.structureMap SecondExampleRankSeven.curve) ≅
      Over.mk (WeierstrassScheme.structureMap (F baseW))) ∧
    TorsionExact (F baseW) ∧ LinearIndependent ℤ fiberPoints ∧
    SecondExampleConductor.conductor hModels=55712032256650048538220027355278990 ∧
    Squarefree (SecondExampleConductor.conductor hModels) := by
  exact ⟨rfl,⟨fiberOverIso⟩,fiber_torsion_exact hMazur,
    fiberPoints_linearIndependent hMazur hReduction,
    SecondExampleConductor.example_conductor hModels hTate,
    SecondExampleConductor.conductor_squarefree hTate (SecondExampleConductor.data hModels)⟩

end
end Z2Z4Rank6.SecondExampleArithmetic
