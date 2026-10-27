module

public import Z2Z4Rank6.SecondJacobianBasic
public import Z2Z4Rank6.BaseCurveArithmetic

@[expose] public section

/-! The printed infinite-order test on the second Jacobian,
Jaswal Theorem 8.1(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6

def secondJacobianP1Double : RationalPoints J2 :=
  .mk ((secondJacobian_equation_iff (984846791588787/8281)
    (23960451532479374042460/753571)).mpr (by norm_num))

theorem secondJacobianP1_double : (2:ℕ) • secondJacobianP1=secondJacobianP1Double := by
  norm_num [secondJacobianP1,secondJacobianP1Double,WeierstrassCurve.Affine.Point.mk,
    two_nsmul,WeierstrassCurve.Affine.Point.add_def,WeierstrassCurve.Affine.Point.add,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,J2]

theorem secondJacobianP1_double_x_den : (984846791588787/8281:ℚ).den=7^2*13^2 := by norm_num

theorem secondJacobian_integral : IntegralWeierstrass J2 := by
  refine ⟨⟨0,1,0,-7927479575830823114160,271658305399029819040875379804308⟩,?_⟩
  ext <;> norm_num [WeierstrassCurve.map,J2]

theorem secondJacobianP1_infinite_order(hSilvermanVII34:OddPrimeTorsionIntegrality):
    ¬IsOfFinAddOrder secondJacobianP1 := by
  intro hP
  have h2:IsOfFinAddOrder secondJacobianP1Double := secondJacobianP1_double ▸ hP.nsmul
  exact (hSilvermanVII34 J2 inferInstance secondJacobian_integral 7 (by decide) (by decide)
    _ _ _ h2) (by norm_num)

theorem secondJacobian_infinite(hSilvermanVII34:OddPrimeTorsionIntegrality):
    Infinite (RationalPoints J2) :=
  Infinite.of_injective (fun n:ℕ=>n • secondJacobianP1)
    (injective_nsmul_iff_not_isOfFinAddOrder.mpr (secondJacobianP1_infinite_order hSilvermanVII34))

end Z2Z4Rank6
