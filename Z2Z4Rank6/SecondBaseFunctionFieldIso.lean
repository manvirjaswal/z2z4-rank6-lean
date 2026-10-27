import Z2Z4Rank6.SecondBaseFunctionFieldEmbeddingData
import Z2Z4Rank6.SecondJacobianFunctionField
import Z2Z4Rank6.QuadraticRatFuncEquiv

/-!
# Q(G2) and printed J2 function fields are Q-algebra isomorphic

The explicit conic/quartic coordinates generate the degree-eight field.
Evaluation at their transcendental x and the quadratic root universal
property construct the field equivalence, with all coordinate images.
-/
namespace Z2Z4Rank6.SecondBaseFunctionFieldIso
noncomputable section

theorem mapped_d : QuadraticRatFuncEquiv.baseEmbedding x x_transcendental
    SecondJacobianFunctionField.d=x^3+x^2-7927479575830823114160*x+
      271658305399029819040875379804308 := by
  simp [SecondJacobianFunctionField.d,map_ofNat]

theorem root_relation : y^2=QuadraticRatFuncEquiv.baseEmbedding x x_transcendental
    SecondJacobianFunctionField.d := equation.trans mapped_d.symm

/-- The equivalence from the printed cubic field to Q(G2). -/
def jacobianFunctionFieldCopyEquiv : SecondJacobianFunctionField.K ≃ₐ[ℚ] K :=
  QuadraticRatFuncEquiv.equiv SecondJacobianFunctionField.d x y x_transcendental
    root_relation field_adjoin_coordinates_eq_top

@[simp] theorem jacobianFunctionFieldCopyEquiv_x : jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.x=x :=
  QuadraticRatFuncEquiv.embedding_X SecondJacobianFunctionField.d x y x_transcendental root_relation

@[simp] theorem jacobianFunctionFieldCopyEquiv_y : jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.y=y :=
  QuadraticRatFuncEquiv.embedding_y SecondJacobianFunctionField.d x y x_transcendental root_relation

theorem jacobianFunctionFieldCopyEquiv_symm_theta : jacobianFunctionFieldCopyEquiv.symm theta=
    secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y := by
  apply jacobianFunctionFieldCopyEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_secondQuarticTheta jacobianFunctionFieldCopyEquiv.toRingHom
    SecondJacobianFunctionField.x SecondJacobianFunctionField.y
  change jacobianFunctionFieldCopyEquiv
      (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y)=
    secondQuarticTheta (jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.x)
      (jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.y) at he
  rw [he,jacobianFunctionFieldCopyEquiv_x,jacobianFunctionFieldCopyEquiv_y,theta_recover]

theorem jacobianFunctionFieldCopyEquiv_symm_eta : jacobianFunctionFieldCopyEquiv.symm eta=
    secondQuarticEta SecondJacobianFunctionField.x SecondJacobianFunctionField.y := by
  apply jacobianFunctionFieldCopyEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have he := map_secondQuarticEta jacobianFunctionFieldCopyEquiv.toRingHom
    SecondJacobianFunctionField.x SecondJacobianFunctionField.y
  change jacobianFunctionFieldCopyEquiv
      (secondQuarticEta SecondJacobianFunctionField.x SecondJacobianFunctionField.y)=
    secondQuarticEta (jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.x)
      (jacobianFunctionFieldCopyEquiv SecondJacobianFunctionField.y) at he
  rw [he,jacobianFunctionFieldCopyEquiv_x,jacobianFunctionFieldCopyEquiv_y,eta_recover]

theorem jacobianFunctionFieldCopyEquiv_symm_s1 : jacobianFunctionFieldCopyEquiv.symm baseS1=
    SecondFamily.thetaS1 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  rw [←s1_recover]
  have he := map_thetaS1 jacobianFunctionFieldCopyEquiv.symm.toRingHom theta
  change jacobianFunctionFieldCopyEquiv.symm (SecondFamily.thetaS1 theta)=
    SecondFamily.thetaS1 (jacobianFunctionFieldCopyEquiv.symm theta) at he
  rw [he,jacobianFunctionFieldCopyEquiv_symm_theta]

theorem jacobianFunctionFieldCopyEquiv_symm_s2 : jacobianFunctionFieldCopyEquiv.symm baseS2=
    SecondFamily.thetaS2 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  rw [←s2_recover]
  have he := map_thetaS2 jacobianFunctionFieldCopyEquiv.symm.toRingHom theta
  change jacobianFunctionFieldCopyEquiv.symm (SecondFamily.thetaS2 theta)=
    SecondFamily.thetaS2 (jacobianFunctionFieldCopyEquiv.symm theta) at he
  rw [he,jacobianFunctionFieldCopyEquiv_symm_theta]

theorem jacobianFunctionFieldCopyEquiv_symm_s3 : jacobianFunctionFieldCopyEquiv.symm baseS3=
    secondEtaToS3 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y)
      (secondQuarticEta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  rw [←s3_recover]
  have he := map_secondEtaToS3 jacobianFunctionFieldCopyEquiv.symm.toRingHom theta eta
  change jacobianFunctionFieldCopyEquiv.symm (secondEtaToS3 theta eta)=
    secondEtaToS3 (jacobianFunctionFieldCopyEquiv.symm theta) (jacobianFunctionFieldCopyEquiv.symm eta) at he
  rw [he,jacobianFunctionFieldCopyEquiv_symm_theta,jacobianFunctionFieldCopyEquiv_symm_eta]

theorem jacobianFunctionFieldCopyEquiv_symm_W : jacobianFunctionFieldCopyEquiv.symm baseW=
    (SecondFamily.thetaS1 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y))^2 := by
  rw [←baseS1_sq,map_pow,jacobianFunctionFieldCopyEquiv_symm_s1]

/-- Composition back to the existing degree-eight quadratic tower. -/
def jacobianFunctionFieldEquiv : SecondJacobianFunctionField.K ≃ₐ[ℚ] SecondFunctionField.K :=
  jacobianFunctionFieldCopyEquiv.trans SecondFunctionFieldCopy.equiv

/-- The equivalence oriented from Q(G2) to the printed J2 field. -/
def secondBaseFunctionFieldEquiv : SecondFunctionField.K ≃ₐ[ℚ] SecondJacobianFunctionField.K :=
  jacobianFunctionFieldEquiv.symm

theorem secondBaseFunctionFieldEquiv_s1 : secondBaseFunctionFieldEquiv SecondFunctionField.s1=
    SecondFamily.thetaS1 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  change jacobianFunctionFieldCopyEquiv.symm
    (SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s1)=_
  have he : SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s1=baseS1 := by
    unfold baseS1 SecondFunctionFieldCopy.s1; rfl
  rw [he,jacobianFunctionFieldCopyEquiv_symm_s1]

theorem secondBaseFunctionFieldEquiv_s2 : secondBaseFunctionFieldEquiv SecondFunctionField.s2=
    SecondFamily.thetaS2 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  change jacobianFunctionFieldCopyEquiv.symm
    (SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s2)=_
  have he : SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s2=baseS2 := by
    unfold baseS2 SecondFunctionFieldCopy.s2; rfl
  rw [he,jacobianFunctionFieldCopyEquiv_symm_s2]

theorem secondBaseFunctionFieldEquiv_s3 : secondBaseFunctionFieldEquiv SecondFunctionField.s3=
    secondEtaToS3 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y)
      (secondQuarticEta SecondJacobianFunctionField.x SecondJacobianFunctionField.y) := by
  change jacobianFunctionFieldCopyEquiv.symm
    (SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s3)=_
  have he : SecondFunctionFieldCopy.equiv.symm SecondFunctionField.s3=baseS3 := by
    unfold baseS3 SecondFunctionFieldCopy.s3; rfl
  rw [he,jacobianFunctionFieldCopyEquiv_symm_s3]

theorem secondBaseFunctionFieldEquiv_W : secondBaseFunctionFieldEquiv SecondFunctionField.W=
    (SecondFamily.thetaS1 (secondQuarticTheta SecondJacobianFunctionField.x SecondJacobianFunctionField.y))^2 := by
  rw [←SecondFunctionField.s1_sq,map_pow,secondBaseFunctionFieldEquiv_s1]

end
end Z2Z4Rank6.SecondBaseFunctionFieldIso
