import Z2Z4Rank6.GJacobianBasic
import Z2Z4Rank6.BaseCurveArithmetic

/-!
# An infinite-order point on the Jacobian printed for G

The triple of the printed point has denominator 17². The hypothesis is Silverman's integrality
statement VII.3.4, as for C.
Source: Jaswal Proposition 7.2(a), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6

def gJacobianP1Double : RationalPoints JG :=
  .mk ((gJacobian_equation_iff 32291 (-5733000)).mpr (by norm_num))
def gJacobianP1Triple : RationalPoints JG :=
  .mk ((gJacobian_equation_iff (-627466/289) (1434756540/4913)).mpr (by norm_num))

theorem gJacobianP1_double : (2:ℕ) • gJacobianP1=gJacobianP1Double := by
  norm_num [gJacobianP1,gJacobianP1Double,WeierstrassCurve.Affine.Point.mk,
    two_nsmul,WeierstrassCurve.Affine.Point.add_def,WeierstrassCurve.Affine.Point.add,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,JG]

theorem gJacobianP1_triple : (3:ℕ) • gJacobianP1=gJacobianP1Triple := by
  rw [show (3:ℕ)=2+1 by decide,add_nsmul,gJacobianP1_double,one_nsmul]
  norm_num [gJacobianP1,gJacobianP1Double,gJacobianP1Triple,WeierstrassCurve.Affine.Point.mk,
    WeierstrassCurve.Affine.Point.add_def,WeierstrassCurve.Affine.Point.add,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,JG]

theorem gJacobianP1_triple_x_den : (-627466/289:ℚ).den=17^2 := by norm_num

theorem gJacobian_integral : IntegralWeierstrass JG := by
  refine ⟨⟨0,1,0,-26097400,38851416548⟩,?_⟩
  ext <;> norm_num [WeierstrassCurve.map,JG]

theorem gJacobianP1_infinite_order (hSilvermanVII34:OddPrimeTorsionIntegrality) :
    ¬IsOfFinAddOrder gJacobianP1 := by
  intro hP
  have h3:IsOfFinAddOrder gJacobianP1Triple := gJacobianP1_triple ▸ hP.nsmul
  exact (hSilvermanVII34 JG inferInstance gJacobian_integral 17 (by decide) (by decide)
    _ _ _ h3) (by norm_num)

theorem gJacobian_infinite (hSilvermanVII34:OddPrimeTorsionIntegrality) :
    Infinite (RationalPoints JG) :=
  Infinite.of_injective (fun n:ℕ=>n • gJacobianP1)
    (injective_nsmul_iff_not_isOfFinAddOrder.mpr (gJacobianP1_infinite_order hSilvermanVII34))

end Z2Z4Rank6
