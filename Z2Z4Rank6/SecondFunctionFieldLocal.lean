module

public import Z2Z4Rank6.SecondFunctionField
public import Z2Z4Rank6.SecondReductionRank
public import Z2Z4Rank6.UnivariateLocal
public import Z2Z4Rank6.FunctionFieldLocal

@[expose] public section

/-!
# A formal place of the degree-eight field Q(G₂)

The three square roots lift with the prescribed nonzero constants at the
printed point θ=857/140. The resulting three quadratic lifts give an
injective field homomorphism into Q((T)), with W=W₀+T.
-/

namespace Z2Z4Rank6.SecondFunctionFieldLocal

open scoped Classical
open SecondReductionData

noncomputable section

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

def WSeries : PS := UnivariateLocal.mSeries baseW

@[simp] theorem WSeries_constant : PowerSeries.constantCoeff WSeries=baseW := by
  simp [WSeries]

theorem root1_constant : baseS1^2=PowerSeries.constantCoeff WSeries := by
  rw [WSeries_constant]
  exact base_on_curve.1

theorem root2_constant : baseS2^2=PowerSeries.constantCoeff
    (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialA) := by
  rw [UnivariateLocal.polynomialSeries_constant]
  norm_num [SecondFunctionField.polynomialA,SecondFamily.beta,baseW,baseS1,baseS2]

theorem root3_constant : baseS3^2=PowerSeries.constantCoeff
    (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialB) := by
  rw [UnivariateLocal.polynomialSeries_constant]
  norm_num [SecondFunctionField.polynomialB,SecondFamily.beta,SecondFamily.gamma,
    baseW,baseS1,baseS3]

def s1Series : PS := Classical.choose (FunctionFieldLocal.exists_square_root_with_constant
  WSeries baseS1 root1_constant (by norm_num [baseS1]))

def s2Series : PS := Classical.choose (FunctionFieldLocal.exists_square_root_with_constant
  (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialA)
  baseS2 root2_constant (by norm_num [baseS2]))

def s3Series : PS := Classical.choose (FunctionFieldLocal.exists_square_root_with_constant
  (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialB)
  baseS3 root3_constant (by norm_num [baseS3]))

theorem s1Series_spec : s1Series^2=WSeries ∧
    PowerSeries.constantCoeff s1Series=baseS1 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    WSeries baseS1 root1_constant (by norm_num [baseS1]))

theorem s2Series_spec : s2Series^2=
    UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialA ∧
    PowerSeries.constantCoeff s2Series=baseS2 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialA)
    baseS2 root2_constant (by norm_num [baseS2]))

theorem s3Series_spec : s3Series^2=
    UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialB ∧
    PowerSeries.constantCoeff s3Series=baseS3 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant
    (UnivariateLocal.polynomialSeries baseW SecondFunctionField.polynomialB)
    baseS3 root3_constant (by norm_num [baseS3]))

def baseEmbedding : SecondFunctionField.Base →+* LS := UnivariateLocal.baseEmbedding baseW

theorem local_s1_relation : (algebraMap PS LS s1Series)^2=
    baseEmbedding SecondFunctionField.dW := by
  rw [← map_pow,s1Series_spec.1]
  exact (UnivariateLocal.baseEmbedding_X baseW).symm

def firstEmbedding : SecondFunctionField.First →+* LS :=
  FunctionFieldLocal.quadraticLift baseEmbedding SecondFunctionField.dW
    (algebraMap PS LS s1Series) local_s1_relation

theorem local_s2_relation : (algebraMap PS LS s2Series)^2=
    firstEmbedding SecondFunctionField.dAFirst := by
  rw [← map_pow,s2Series_spec.1]
  simp only [firstEmbedding,SecondFunctionField.dAFirst,
    FunctionFieldLocal.quadraticLift_algebraMap]
  have h := UnivariateLocal.baseEmbedding_polynomial baseW SecondFunctionField.polynomialA
  rw [SecondFunctionField.polynomialA_image] at h
  exact h.symm

def secondEmbedding : SecondFunctionField.Second →+* LS :=
  FunctionFieldLocal.quadraticLift firstEmbedding SecondFunctionField.dAFirst
    (algebraMap PS LS s2Series) local_s2_relation

theorem local_s3_relation : (algebraMap PS LS s3Series)^2=
    secondEmbedding SecondFunctionField.dBSecond := by
  rw [← map_pow,s3Series_spec.1]
  simp only [secondEmbedding,SecondFunctionField.dBSecond,
    SecondFunctionField.dBFirst,firstEmbedding,FunctionFieldLocal.quadraticLift_algebraMap]
  have h := UnivariateLocal.baseEmbedding_polynomial baseW SecondFunctionField.polynomialB
  rw [SecondFunctionField.polynomialB_image] at h
  exact h.symm

/-- The embedding of Q(G₂), selecting all three printed root signs. -/
def embedding : SecondFunctionField.K →+* LS :=
  FunctionFieldLocal.quadraticLift secondEmbedding SecondFunctionField.dBSecond
    (algebraMap PS LS s3Series) local_s3_relation

theorem embedding_injective : Function.Injective embedding := embedding.injective

@[simp] theorem embedding_base (r : SecondFunctionField.Base) :
    embedding (algebraMap SecondFunctionField.Base SecondFunctionField.K r)=baseEmbedding r := by
  rw [IsScalarTower.algebraMap_apply SecondFunctionField.Base SecondFunctionField.Second
    SecondFunctionField.K,IsScalarTower.algebraMap_apply SecondFunctionField.Base
    SecondFunctionField.First SecondFunctionField.Second]
  simp [embedding,secondEmbedding,firstEmbedding]

@[simp] theorem embedding_W : embedding SecondFunctionField.W=algebraMap PS LS WSeries := by
  simp [SecondFunctionField.W,baseEmbedding,WSeries]

@[simp] theorem embedding_s1 : embedding SecondFunctionField.s1=algebraMap PS LS s1Series := by
  rw [SecondFunctionField.s1,IsScalarTower.algebraMap_apply SecondFunctionField.First
    SecondFunctionField.Second SecondFunctionField.K]
  simp [embedding,secondEmbedding,firstEmbedding]

@[simp] theorem embedding_s2 : embedding SecondFunctionField.s2=algebraMap PS LS s2Series := by
  simp [SecondFunctionField.s2,embedding,secondEmbedding]

@[simp] theorem embedding_s3 : embedding SecondFunctionField.s3=algebraMap PS LS s3Series := by
  simp [SecondFunctionField.s3,embedding]

end
end Z2Z4Rank6.SecondFunctionFieldLocal
