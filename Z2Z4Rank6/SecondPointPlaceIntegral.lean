import Z2Z4Rank6.RigidRationalPlace
import Z2Z4Rank6.LaurentRootIntegral
import Z2Z4Rank6.SecondFunctionFieldPointPlace

/-! Every normalized rational Laurent place of Q(G2) has three integral
root images. Their constant coefficients reconstruct the affine point;
first coefficients rule out all three ramified parameter values. -/
namespace Z2Z4Rank6.SecondPointPlaceEquiv
noncomputable section
open Polynomial SecondFamily
abbrev PS := PowerSeries ℚ
abbrev LS := LaurentSeries ℚ
abbrev Place := RigidRationalPlace SecondFunctionField.K
abbrev Point := SecondFunctionFieldPointPlace.Point

def parameterSeries (v : Place) : PS := UnivariateLocal.mSeries v.parameter
def aSeries (v : Place) : PS := UnivariateLocal.polynomialSeries v.parameter SecondFunctionField.polynomialA
def bSeries (v : Place) : PS := UnivariateLocal.polynomialSeries v.parameter SecondFunctionField.polynomialB

@[simp] theorem parameterSeries_constant (v : Place) :
    PowerSeries.constantCoeff (parameterSeries v)=v.parameter := by simp [parameterSeries]
@[simp] theorem aSeries_constant (v : Place) :
    PowerSeries.constantCoeff (aSeries v)=qA v.parameter := by
  simp [aSeries,SecondFunctionField.polynomialA,qA]
@[simp] theorem bSeries_constant (v : Place) :
    PowerSeries.constantCoeff (bSeries v)=qB v.parameter := by
  simp [bSeries,SecondFunctionField.polynomialB,qB]

@[simp] theorem embedding_W (v : Place) :
    v.embedding SecondFunctionField.W=algebraMap PS LS (parameterSeries v) := v.rigid

theorem embedding_polynomial (v : Place) (p : ℚ[X]) :
    v.embedding (aeval SecondFunctionField.W p)=
      algebraMap PS LS (UnivariateLocal.polynomialSeries v.parameter p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,aeval_C,aeval_X,
      UnivariateLocal.polynomialSeries_C,UnivariateLocal.polynomialSeries_X,
      AlgHom.commutes,embedding_W,parameterSeries]
    rfl

theorem embedding_s1_sq (v : Place) :
    (v.embedding SecondFunctionField.s1)^2=algebraMap PS LS (parameterSeries v) := by
  rw [←map_pow,SecondFunctionField.s1_sq,embedding_W]

theorem embedding_s2_sq (v : Place) :
    (v.embedding SecondFunctionField.s2)^2=algebraMap PS LS (aSeries v) := by
  rw [←map_pow,SecondFunctionField.s2_sq]
  have hp : aeval SecondFunctionField.W SecondFunctionField.polynomialA=
      qA SecondFunctionField.W := by
    norm_num [SecondFunctionField.polynomialA,qA,beta]
  rw [←hp]
  exact embedding_polynomial v _

theorem embedding_s3_sq (v : Place) :
    (v.embedding SecondFunctionField.s3)^2=algebraMap PS LS (bSeries v) := by
  rw [←map_pow,SecondFunctionField.s3_sq]
  have hp : aeval SecondFunctionField.W SecondFunctionField.polynomialB=
      qB SecondFunctionField.W := by
    norm_num [SecondFunctionField.polynomialB,qB,beta,gamma]
  rw [←hp]
  exact embedding_polynomial v _

def s1Series (v : Place) : PS := Classical.choose
  (exists_powerSeries_of_square (v.embedding SecondFunctionField.s1) (parameterSeries v) (embedding_s1_sq v))
def s2Series (v : Place) : PS := Classical.choose
  (exists_powerSeries_of_square (v.embedding SecondFunctionField.s2) (aSeries v) (embedding_s2_sq v))
def s3Series (v : Place) : PS := Classical.choose
  (exists_powerSeries_of_square (v.embedding SecondFunctionField.s3) (bSeries v) (embedding_s3_sq v))

theorem s1Series_image (v : Place) : algebraMap PS LS (s1Series v)=v.embedding SecondFunctionField.s1 :=
  Classical.choose_spec (exists_powerSeries_of_square (v.embedding SecondFunctionField.s1) (parameterSeries v) (embedding_s1_sq v))
theorem s2Series_image (v : Place) : algebraMap PS LS (s2Series v)=v.embedding SecondFunctionField.s2 :=
  Classical.choose_spec (exists_powerSeries_of_square (v.embedding SecondFunctionField.s2) (aSeries v) (embedding_s2_sq v))
theorem s3Series_image (v : Place) : algebraMap PS LS (s3Series v)=v.embedding SecondFunctionField.s3 :=
  Classical.choose_spec (exists_powerSeries_of_square (v.embedding SecondFunctionField.s3) (bSeries v) (embedding_s3_sq v))

theorem s1Series_sq (v : Place) : (s1Series v)^2=parameterSeries v := by
  apply IsFractionRing.injective PS LS
  rw [map_pow,s1Series_image,embedding_s1_sq]
theorem s2Series_sq (v : Place) : (s2Series v)^2=aSeries v := by
  apply IsFractionRing.injective PS LS
  rw [map_pow,s2Series_image,embedding_s2_sq]
theorem s3Series_sq (v : Place) : (s3Series v)^2=bSeries v := by
  apply IsFractionRing.injective PS LS
  rw [map_pow,s3Series_image,embedding_s3_sq]

def toG2Point (v : Place) : G2Point ℚ where
  W:=v.parameter
  s1:=PowerSeries.constantCoeff (s1Series v)
  s2:=PowerSeries.constantCoeff (s2Series v)
  s3:=PowerSeries.constantCoeff (s3Series v)
  s1_sq:=by simpa using congrArg PowerSeries.constantCoeff (s1Series_sq v)
  s2_sq:=by simpa using congrArg PowerSeries.constantCoeff (s2Series_sq v)
  s3_sq:=by simpa using congrArg PowerSeries.constantCoeff (s3Series_sq v)

private theorem constant_ne_zero_of_coeff_one {f a : PS} (hs : a^2=f)
    (h1 : PowerSeries.coeff 1 f≠0) : PowerSeries.constantCoeff a≠0 := by
  intro h0
  apply h1
  rw [←hs,sq,PowerSeries.coeff_one_mul,h0,mul_zero,zero_add]

 theorem s1_constant_ne_zero (v : Place) : PowerSeries.constantCoeff (s1Series v)≠0 := by
  apply constant_ne_zero_of_coeff_one (s1Series_sq v)
  simp [parameterSeries]
 theorem s2_constant_ne_zero (v : Place) : PowerSeries.constantCoeff (s2Series v)≠0 := by
  apply constant_ne_zero_of_coeff_one (s2Series_sq v)
  simp [aSeries,SecondFunctionField.polynomialA]
 theorem s3_constant_ne_zero (v : Place) : PowerSeries.constantCoeff (s3Series v)≠0 := by
  apply constant_ne_zero_of_coeff_one (s3Series_sq v)
  norm_num [bSeries,UnivariateLocal.polynomialSeries_coeff,SecondFunctionField.polynomialB,beta]

 theorem parameter_ne_zero (v : Place) : v.parameter≠0 := by
  change (toG2Point v).W≠0
  rw [←(toG2Point v).s1_sq]
  exact pow_ne_zero 2 (s1_constant_ne_zero v)
 theorem parameter_ne_beta (v : Place) : v.parameter≠(beta:ℚ) := by
  intro h
  have he := (toG2Point v).s2_sq
  change PowerSeries.constantCoeff (s2Series v)^2=qA v.parameter at he
  rw [h,qA,sub_self,mul_zero] at he
  exact pow_ne_zero 2 (s2_constant_ne_zero v) he
 theorem parameter_ne_gamma (v : Place) : v.parameter≠(gamma:ℚ) := by
  intro h
  have he := (toG2Point v).s3_sq
  change PowerSeries.constantCoeff (s3Series v)^2=qB v.parameter at he
  rw [h,qB,sub_self,mul_zero] at he
  exact pow_ne_zero 2 (s3_constant_ne_zero v) he

def toPoint (v : Place) : Point := ⟨toG2Point v,
  parameter_ne_zero v,parameter_ne_beta v,parameter_ne_gamma v⟩
@[simp] theorem toPoint_W (v : Place) : (toPoint v).val.W=v.parameter := rfl
end
end Z2Z4Rank6.SecondPointPlaceEquiv
