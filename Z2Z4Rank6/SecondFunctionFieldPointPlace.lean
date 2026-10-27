import Z2Z4Rank6.SecondFunctionField
import Z2Z4Rank6.FunctionFieldLocal
import Z2Z4Rank6.UnivariateLocal
import Z2Z4Rank6.SecondJInvariant

/-!
# Rigid Laurent places at unramified G2 rational points

At P substitute W=P.W+T and lift the three square roots with constants
P.s1,P.s2,P.s3. This constructs a Q-algebra embedding of Q(G2) in
Q((T)). The excluded
branch-coordinate fibers are finite. Source: Jaswal Theorem 8.1(c),
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.SecondFunctionFieldPointPlace
noncomputable section
open SecondFamily

abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ

/-- The three branch values are excluded only for the prescribed simple-root
Hensel chart. -/
abbrev Point := {P : G2Point ℚ // P.W≠0 ∧ P.W≠(beta:ℚ) ∧ P.W≠(gamma:ℚ)}

theorem s1_ne_zero (P : Point) : P.val.s1≠0 := by
  intro h
  apply P.property.1
  rw [←P.val.s1_sq,h]
  norm_num

theorem s2_ne_zero (P : Point) : P.val.s2≠0 := by
  intro h
  have he := P.val.s2_sq
  rw [h] at he
  have hW : P.val.W=(beta:ℚ) := by
    norm_num [qA] at he
    linarith
  exact P.property.2.1 hW

theorem s3_ne_zero (P : Point) : P.val.s3≠0 := by
  intro h
  have he := P.val.s3_sq
  rw [h] at he
  have hW : P.val.W=(gamma:ℚ) := by
    norm_num [qB,beta,gamma] at he ⊢
    linarith
  exact P.property.2.2 hW

def WSeries (P : Point) : PS := UnivariateLocal.mSeries P.val.W
@[simp] theorem WSeries_constant (P : Point) : PowerSeries.constantCoeff (WSeries P)=P.val.W :=
  UnivariateLocal.mSeries_constant _

def aSeries (P : Point) : PS :=
  UnivariateLocal.polynomialSeries P.val.W SecondFunctionField.polynomialA

def bSeries (P : Point) : PS :=
  UnivariateLocal.polynomialSeries P.val.W SecondFunctionField.polynomialB

@[simp] theorem aSeries_constant (P : Point) : PowerSeries.constantCoeff (aSeries P)=qA P.val.W := by
  simp [aSeries,SecondFunctionField.polynomialA,qA]

@[simp] theorem bSeries_constant (P : Point) : PowerSeries.constantCoeff (bSeries P)=qB P.val.W := by
  simp [bSeries,SecondFunctionField.polynomialB,qB]

def s1Series (P : Point) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (WSeries P) P.val.s1
    (by simpa using P.val.s1_sq) (s1_ne_zero P))
def s2Series (P : Point) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (aSeries P) P.val.s2
    (by simpa using P.val.s2_sq) (s2_ne_zero P))
def s3Series (P : Point) : PS := Classical.choose
  (FunctionFieldLocal.exists_square_root_with_constant (bSeries P) P.val.s3
    (by simpa using P.val.s3_sq) (s3_ne_zero P))

theorem s1Series_spec (P : Point) : (s1Series P)^2=WSeries P ∧ PowerSeries.constantCoeff (s1Series P)=P.val.s1 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant (WSeries P) P.val.s1
    (by simpa using P.val.s1_sq) (s1_ne_zero P))
theorem s2Series_spec (P : Point) : (s2Series P)^2=aSeries P ∧ PowerSeries.constantCoeff (s2Series P)=P.val.s2 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant (aSeries P) P.val.s2
    (by simpa using P.val.s2_sq) (s2_ne_zero P))
theorem s3Series_spec (P : Point) : (s3Series P)^2=bSeries P ∧ PowerSeries.constantCoeff (s3Series P)=P.val.s3 :=
  Classical.choose_spec (FunctionFieldLocal.exists_square_root_with_constant (bSeries P) P.val.s3
    (by simpa using P.val.s3_sq) (s3_ne_zero P))

@[simp] theorem s1Series_constant (P : Point) : PowerSeries.constantCoeff (s1Series P)=P.val.s1 := (s1Series_spec P).2
@[simp] theorem s2Series_constant (P : Point) : PowerSeries.constantCoeff (s2Series P)=P.val.s2 := (s2Series_spec P).2
@[simp] theorem s3Series_constant (P : Point) : PowerSeries.constantCoeff (s3Series P)=P.val.s3 := (s3Series_spec P).2

abbrev baseEmbedding (P : Point) : SecondFunctionField.Base→+*LS := UnivariateLocal.baseEmbedding P.val.W

private theorem local_s1_relation (P : Point) :
    (algebraMap PS LS (s1Series P))^2=baseEmbedding P SecondFunctionField.dW := by
  rw [←map_pow,(s1Series_spec P).1]
  simp [baseEmbedding,SecondFunctionField.dW,WSeries]

def firstEmbedding (P : Point) : SecondFunctionField.First→+*LS :=
  FunctionFieldLocal.quadraticLift (baseEmbedding P) SecondFunctionField.dW
    (algebraMap PS LS (s1Series P)) (local_s1_relation P)

private theorem local_s2_relation (P : Point) :
    (algebraMap PS LS (s2Series P))^2=firstEmbedding P SecondFunctionField.dAFirst := by
  rw [←map_pow,(s2Series_spec P).1]
  simp only [SecondFunctionField.dAFirst,firstEmbedding,FunctionFieldLocal.quadraticLift_algebraMap]
  rw [←SecondFunctionField.polynomialA_image]
  exact (UnivariateLocal.baseEmbedding_polynomial P.val.W SecondFunctionField.polynomialA).symm

def secondEmbedding (P : Point) : SecondFunctionField.Second→+*LS :=
  FunctionFieldLocal.quadraticLift (firstEmbedding P) SecondFunctionField.dAFirst
    (algebraMap PS LS (s2Series P)) (local_s2_relation P)

private theorem local_s3_relation (P : Point) :
    (algebraMap PS LS (s3Series P))^2=secondEmbedding P SecondFunctionField.dBSecond := by
  rw [←map_pow,(s3Series_spec P).1]
  simp only [SecondFunctionField.dBSecond,SecondFunctionField.dBFirst,secondEmbedding,
    firstEmbedding,FunctionFieldLocal.quadraticLift_algebraMap]
  rw [←SecondFunctionField.polynomialB_image]
  exact (UnivariateLocal.baseEmbedding_polynomial P.val.W SecondFunctionField.polynomialB).symm

/-- The field embedding at the rational G2 point. -/
def embedding (P : Point) : SecondFunctionField.K→+*LS :=
  FunctionFieldLocal.quadraticLift (secondEmbedding P) SecondFunctionField.dBSecond
    (algebraMap PS LS (s3Series P)) (local_s3_relation P)

theorem embedding_injective (P : Point) : Function.Injective (embedding P) := (embedding P).injective

@[simp] theorem embedding_base (P : Point) (r : SecondFunctionField.Base) :
    embedding P (algebraMap SecondFunctionField.Base SecondFunctionField.K r)=baseEmbedding P r := by
  rw [IsScalarTower.algebraMap_apply SecondFunctionField.Base SecondFunctionField.Second SecondFunctionField.K,
    IsScalarTower.algebraMap_apply SecondFunctionField.Base SecondFunctionField.First SecondFunctionField.Second]
  simp [embedding,secondEmbedding,firstEmbedding]

@[simp] theorem embedding_W (P : Point) :
    embedding P SecondFunctionField.W=algebraMap PS LS (WSeries P) := by
  simp [SecondFunctionField.W,WSeries]

@[simp] theorem embedding_s1 (P : Point) :
    embedding P SecondFunctionField.s1=algebraMap PS LS (s1Series P) := by
  rw [SecondFunctionField.s1,
    IsScalarTower.algebraMap_apply SecondFunctionField.First SecondFunctionField.Second SecondFunctionField.K]
  simp [embedding,secondEmbedding,firstEmbedding]

@[simp] theorem embedding_s2 (P : Point) :
    embedding P SecondFunctionField.s2=algebraMap PS LS (s2Series P) := by
  simp [SecondFunctionField.s2,embedding,secondEmbedding]

@[simp] theorem embedding_s3 (P : Point) :
    embedding P SecondFunctionField.s3=algebraMap PS LS (s3Series P) := by
  simp [SecondFunctionField.s3,embedding]

def embeddingAlgHom (P : Point) : SecondFunctionField.K→ₐ[ℚ]LS where
  toRingHom:=embedding P
  commutes' q:=RingHom.map_rat_algebraMap (embedding P) q

@[simp] theorem embeddingAlgHom_apply (P : Point) (x : SecondFunctionField.K) :
    embeddingAlgHom P x=embedding P x := rfl

theorem embeddingAlgHom_parameter (P : Point) :
    embeddingAlgHom P (algebraMap (RatFunc ℚ) SecondFunctionField.K RatFunc.X)=
      algebraMap PS LS (PowerSeries.C P.val.W+PowerSeries.X) := embedding_W P

theorem embedding_uniformizer (P : Point) :
    embedding P (SecondFunctionField.W-algebraMap ℚ SecondFunctionField.K P.val.W)=
      algebraMap PS LS PowerSeries.X := by
  rw [map_sub,embedding_W,RingHom.map_rat_algebraMap]
  change algebraMap PS LS (WSeries P)-algebraMap PS LS (PowerSeries.C P.val.W)=_
  rw [←map_sub]
  congr 1
  dsimp [WSeries,UnivariateLocal.mSeries]
  ring

theorem embedding_injective_on_points : Function.Injective embedding := by
  intro P Q h
  have hW := congrArg (fun f : SecondFunctionField.K→+*LS => f SecondFunctionField.W) h
  have h1 := congrArg (fun f : SecondFunctionField.K→+*LS => f SecondFunctionField.s1) h
  have h2 := congrArg (fun f : SecondFunctionField.K→+*LS => f SecondFunctionField.s2) h
  have h3 := congrArg (fun f : SecondFunctionField.K→+*LS => f SecondFunctionField.s3) h
  rw [embedding_W,embedding_W] at hW
  rw [embedding_s1,embedding_s1] at h1
  rw [embedding_s2,embedding_s2] at h2
  rw [embedding_s3,embedding_s3] at h3
  have hW' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) hW)
  have h1' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) h1)
  have h2' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) h2)
  have h3' := congrArg PowerSeries.constantCoeff ((IsFractionRing.injective PS LS) h3)
  apply Subtype.ext
  apply G2Point.ext
  · simpa using hW'
  · simpa using h1'
  · simpa using h2'
  · simpa using h3'

theorem embeddingAlgHom_injective_on_points : Function.Injective embeddingAlgHom := by
  intro P Q h
  apply embedding_injective_on_points
  exact congrArg AlgHom.toRingHom h

def branchPoints : Set (G2Point ℚ) := {P | P.W=0 ∨ P.W=(beta:ℚ) ∨ P.W=(gamma:ℚ)}

theorem branchPoints_finite : branchPoints.Finite := by
  have he : branchPoints={P : G2Point ℚ | P.W=0}∪{P | P.W=(beta:ℚ)}∪{P | P.W=(gamma:ℚ)} := by
    ext P
    simp [branchPoints,or_assoc]
  rw [he]
  exact ((finite_G2Point_W_fiber 0).union (finite_G2Point_W_fiber beta)).union (finite_G2Point_W_fiber gamma)

end
end Z2Z4Rank6.SecondFunctionFieldPointPlace
