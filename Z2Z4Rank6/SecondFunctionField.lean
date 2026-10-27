import Z2Z4Rank6.SecondSections
import Z2Z4Rank6.FunctionField

/-!
# The degree-eight function field of G₂

Section 8 of M. Jaswal, "Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six", DOI 10.5281/zenodo.23437117.

The field is a tower of three quadratic algebras over Q(W), with the
three printed square relations. This file
constructs the six generic points, without claiming independence.
-/

namespace Z2Z4Rank6.SecondFunctionField

open Polynomial SecondFamily

noncomputable section

set_option maxHeartbeats 400000

theorem map_lambda {L M : Type*} [Field L] [Field M] (f : L →+* M) :
    f (lambda : L)=(lambda : M) := by
  simp only [lambda,map_div₀,map_ofNat]

theorem map_beta {L M : Type*} [Field L] [Field M] (f : L →+* M) :
    f (beta : L)=(beta : M) := by
  simp only [beta,map_pow,map_div₀,map_ofNat]

theorem map_gamma {L M : Type*} [Field L] [Field M] (f : L →+* M) :
    f (gamma : L)=(gamma : M) := by
  simp only [gamma,map_pow,map_div₀,map_ofNat]

theorem one_add_lambda_ne_zero {L : Type*} [Field L] [CharZero L] :
    1+(lambda : L) ≠ 0 := by norm_num [lambda]

/-- Odd polynomial degree excludes a square in its rational-function field.
Integral closedness first brings a putative rational-function root back into
the polynomial ring. -/
theorem not_isSquare_fraction_of_odd_natDegree {F : Type*} [Field F]
    (p : F[X]) (hp : Odd p.natDegree) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨z,hz⟩
  have hint : IsIntegral F[X] (z^2) := by
    rw [sq, ← hz]
    exact isIntegral_algebraMap
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=F[X]) (by decide : 0 < (2:ℕ)) hint
  have heq : p=r*r := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_mul,hr] using hz
  have hr0 : r ≠ 0 := by
    intro h
    rw [heq,h,mul_zero] at hp
    norm_num at hp
  have hd := congrArg Polynomial.natDegree heq
  rw [natDegree_mul hr0 hr0] at hd
  obtain ⟨n,hn⟩ := hp
  omega

/-- A scalar remains nonsquare after adjoining sqrt(d₁),sqrt(d₂) if its four
possible base square classes remain nonsquare. This is the general iterated quadratic criterion. -/
theorem not_isSquare_in_biquadratic {L : Type*} [Field L] [CharZero L]
    (d1 d2 e : L) (h1 : ¬ IsSquare d1)
    (he : ¬ IsSquare e) (h1e : ¬ IsSquare (d1*e))
    (h2e : ¬ IsSquare (d2*e)) (h12e : ¬ IsSquare (d1*(d2*e))) :
    ¬ IsSquare (algebraMap (QuadraticAlgebra L d1 0)
      (QuadraticAlgebra (QuadraticAlgebra L d1 0)
        (algebraMap L (QuadraticAlgebra L d1 0) d2) 0)
      (algebraMap L (QuadraticAlgebra L d1 0) e)) := by
  let : Fact (¬ IsSquare d1) := ⟨h1⟩
  apply FunctionField.not_isSquare_in_quadratic
    (algebraMap L (QuadraticAlgebra L d1 0) d2)
    (algebraMap L (QuadraticAlgebra L d1 0) e)
  · exact FunctionField.not_isSquare_in_quadratic d1 e he h1e
  · simpa only [← map_mul] using
      FunctionField.not_isSquare_in_quadratic d1 (d2*e) h2e h12e

abbrev Base := RatFunc ℚ

def polynomialW : ℚ[X] := Polynomial.X
def polynomialA : ℚ[X] := C 29*(Polynomial.X-C beta)
def polynomialB : ℚ[X] := C (-29*beta)*(Polynomial.X-C gamma)

def dW : Base := RatFunc.X
def dA : Base := qA RatFunc.X
def dB : Base := qB RatFunc.X

theorem polynomialW_image : algebraMap ℚ[X] Base polynomialW=dW := by
  simp [polynomialW,dW,RatFunc.algebraMap_X]

theorem polynomialA_image : algebraMap ℚ[X] Base polynomialA=dA := by
  norm_num [polynomialA,dA,qA,beta,RatFunc.algebraMap_X]

theorem polynomialB_image : algebraMap ℚ[X] Base polynomialB=dB := by
  norm_num [polynomialB,dB,qB,beta,gamma,RatFunc.algebraMap_X]

theorem polynomialW_degree : polynomialW.natDegree=1 := by simp [polynomialW]
theorem polynomialA_degree : polynomialA.natDegree=1 := by
  rw [polynomialA,natDegree_C_mul (by norm_num)]
  exact natDegree_X_sub_C _
theorem polynomialB_degree : polynomialB.natDegree=1 := by
  rw [polynomialB,natDegree_C_mul (by norm_num [beta])]
  exact natDegree_X_sub_C _

theorem polynomialW_leadingCoeff : polynomialW.leadingCoeff=1 := by simp [polynomialW]
theorem polynomialA_leadingCoeff : polynomialA.leadingCoeff=29 := by
  simp [polynomialA,leadingCoeff_mul]
theorem polynomialB_leadingCoeff : polynomialB.leadingCoeff=-29*beta := by
  simp [polynomialB,leadingCoeff_mul]

theorem polynomialW_ne_zero : polynomialW ≠ 0 := by simp [polynomialW]
theorem polynomialA_ne_zero : polynomialA ≠ 0 := by
  exact leadingCoeff_ne_zero.mp (by rw [polynomialA_leadingCoeff]; norm_num)
theorem polynomialB_ne_zero : polynomialB ≠ 0 := by
  exact leadingCoeff_ne_zero.mp (by rw [polynomialB_leadingCoeff]; norm_num [beta])

theorem dW_not_isSquare : ¬ IsSquare dW := by
  rw [← polynomialW_image]
  apply not_isSquare_fraction_of_odd_natDegree
  rw [polynomialW_degree]
  decide

theorem dA_not_isSquare : ¬ IsSquare dA := by
  rw [← polynomialA_image]
  apply not_isSquare_fraction_of_odd_natDegree
  rw [polynomialA_degree]
  decide

theorem dB_not_isSquare : ¬ IsSquare dB := by
  rw [← polynomialB_image]
  apply not_isSquare_fraction_of_odd_natDegree
  rw [polynomialB_degree]
  decide

theorem dW_mul_dA_not_isSquare : ¬ IsSquare (dW*dA) := by
  rw [← polynomialW_image,← polynomialA_image,← map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [leadingCoeff_mul,polynomialW_leadingCoeff,polynomialA_leadingCoeff]
  norm_num

theorem dW_mul_dB_not_isSquare : ¬ IsSquare (dW*dB) := by
  rw [← polynomialW_image,← polynomialB_image,← map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [leadingCoeff_mul,polynomialW_leadingCoeff,polynomialB_leadingCoeff]
  norm_num [beta]

theorem dA_mul_dB_not_isSquare : ¬ IsSquare (dA*dB) := by
  rw [← polynomialA_image,← polynomialB_image,← map_mul]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [leadingCoeff_mul,polynomialA_leadingCoeff,polynomialB_leadingCoeff]
  norm_num [beta]

theorem dW_mul_dA_mul_dB_not_isSquare : ¬ IsSquare (dW*(dA*dB)) := by
  rw [← polynomialW_image,← polynomialA_image,← polynomialB_image,← map_mul,← map_mul]
  apply not_isSquare_fraction_of_odd_natDegree
  rw [natDegree_mul polynomialW_ne_zero (mul_ne_zero polynomialA_ne_zero polynomialB_ne_zero),
    natDegree_mul polynomialA_ne_zero polynomialB_ne_zero,
    polynomialW_degree,polynomialA_degree,polynomialB_degree]
  decide

instance dW_nonsquare_fact : Fact (¬ IsSquare dW) := ⟨dW_not_isSquare⟩
abbrev First := QuadraticAlgebra Base dW 0

def dAFirst : First := algebraMap Base First dA
def dBFirst : First := algebraMap Base First dB

theorem dAFirst_not_isSquare : ¬ IsSquare dAFirst :=
  FunctionField.not_isSquare_in_quadratic dW dA dA_not_isSquare dW_mul_dA_not_isSquare

theorem dBFirst_not_isSquare : ¬ IsSquare dBFirst :=
  FunctionField.not_isSquare_in_quadratic dW dB dB_not_isSquare dW_mul_dB_not_isSquare

theorem dAFirst_mul_dBFirst_not_isSquare : ¬ IsSquare (dAFirst*dBFirst) := by
  simpa only [dAFirst,dBFirst,← map_mul] using
    FunctionField.not_isSquare_in_quadratic dW (dA*dB)
      dA_mul_dB_not_isSquare dW_mul_dA_mul_dB_not_isSquare

instance dAFirst_nonsquare_fact : Fact (¬ IsSquare dAFirst) := ⟨dAFirst_not_isSquare⟩
abbrev Second := QuadraticAlgebra First dAFirst 0

def dBSecond : Second := algebraMap First Second dBFirst

/-- The third square class remains nonsquare after the first two adjunctions.
This applies the two-coefficient quadratic criterion twice, using the four
base classes dB, dW*dB, dA*dB and dW*dA*dB. -/
theorem dBSecond_not_isSquare : ¬ IsSquare dBSecond :=
  not_isSquare_in_biquadratic dW dA dB dW_not_isSquare
    dB_not_isSquare dW_mul_dB_not_isSquare dA_mul_dB_not_isSquare
    dW_mul_dA_mul_dB_not_isSquare

instance dBSecond_nonsquare_fact : Fact (¬ IsSquare dBSecond) := ⟨dBSecond_not_isSquare⟩

/-- The function field Q(G₂). -/
abbrev K := QuadraticAlgebra Second dBSecond 0

def W : K := algebraMap Base K RatFunc.X
def s1 : K := algebraMap First K (QuadraticAlgebra.omega : First)
def s2 : K := algebraMap Second K (QuadraticAlgebra.omega : Second)
def s3 : K := QuadraticAlgebra.omega

theorem first_finrank : Module.finrank Base First=2 := QuadraticAlgebra.finrank_eq_two _ _
theorem second_finrank : Module.finrank First Second=2 := QuadraticAlgebra.finrank_eq_two _ _
theorem third_finrank : Module.finrank Second K=2 := QuadraticAlgebra.finrank_eq_two _ _

theorem finrank_eq_eight : Module.finrank Base K=8 := by
  rw [← Module.finrank_mul_finrank Base Second K,
    ← Module.finrank_mul_finrank Base First Second,
    first_finrank,second_finrank,third_finrank]

theorem W_transcendental : Transcendental ℚ W := by
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem s1_sq : s1^2=W := by
  rw [s1,← map_pow]
  have hroot : (QuadraticAlgebra.omega : First)^2=algebraMap Base First dW := by
    rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hroot,← IsScalarTower.algebraMap_apply Base First K]
  rfl

theorem s2_sq : s2^2=qA W := by
  rw [s2,← map_pow]
  have hroot : (QuadraticAlgebra.omega : Second)^2=algebraMap First Second dAFirst := by
    rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hroot,← IsScalarTower.algebraMap_apply First Second K]
  change algebraMap First K (algebraMap Base First dA)=_
  rw [← IsScalarTower.algebraMap_apply Base First K]
  norm_num [dA,qA,beta,W,map_ofNat]

theorem s3_sq : s3^2=qB W := by
  have hroot : s3^2=algebraMap Second K dBSecond := by
    rw [s3,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [hroot]
  change algebraMap Second K (algebraMap First Second (algebraMap Base First dB))=_
  rw [← IsScalarTower.algebraMap_apply First Second K,
    ← IsScalarTower.algebraMap_apply Base First K]
  norm_num [dB,qB,beta,gamma,W,map_ofNat]

/-- The explicit eight-element quadratic tower basis. -/
def basis : Module.Basis ((Fin 2 × Fin 2) × Fin 2) Base K :=
  ((QuadraticAlgebra.basis dW 0).smulTower
    (QuadraticAlgebra.basis dAFirst 0)).smulTower (QuadraticAlgebra.basis dBSecond 0)

theorem quadratic_expansion {R : Type*} [CommRing R] {a b : R}
    (z : QuadraticAlgebra R a b) :
    z=algebraMap R (QuadraticAlgebra R a b) z.re+
      algebraMap R (QuadraticAlgebra R a b) z.im*QuadraticAlgebra.omega := by
  simpa only [Algebra.smul_def,mul_one] using
    (QuadraticAlgebra.re_smul_add_im_smul z).symm

/-- Polynomial evaluation at W agrees with the embedding through Q(W). -/
theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base K (algebraMap ℚ[X] Base p)=aeval W p := by
  have hC : (algebraMap Base K).comp (RatFunc.C : ℚ →+* Base)=algebraMap ℚ K :=
    Subsingleton.elim _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r =>
    have hr := RingHom.congr_fun hC r
    simp only [RingHom.comp_apply] at hr
    simp only [RatFunc.algebraMap_monomial,map_mul,map_pow,aeval_monomial,W,hr]

/-- Every element of the constructed field is in Q(W,s₁,s₂,s₃). -/
theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({W,s1,s2,s3} : Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({W,s1,s2,s3} : Set K)
  have hW : W ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have h1 : s1 ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have h2 : s2 ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have h3 : s3 ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hsimple : IntermediateField.adjoin ℚ ({W} : Set K) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hW
  have hbase (r : Base) : algebraMap Base K r ∈ S := by
    apply hsimple
    induction r using RatFunc.induction_on with
    | _ p q hq =>
      apply (IntermediateField.mem_adjoin_simple_iff ℚ _).mpr
      exact ⟨p,q,by rw [map_div₀,polynomial_embedding,polynomial_embedding]⟩
  have hfirst (z : First) : algebraMap First K z ∈ S := by
    rw [quadratic_expansion z,map_add,map_mul,
      ← IsScalarTower.algebraMap_apply Base First K,
      ← IsScalarTower.algebraMap_apply Base First K]
    exact add_mem (hbase _) (mul_mem (hbase _) h1)
  have hsecond (z : Second) : algebraMap Second K z ∈ S := by
    rw [quadratic_expansion z,map_add,map_mul,
      ← IsScalarTower.algebraMap_apply First Second K,
      ← IsScalarTower.algebraMap_apply First Second K]
    exact add_mem (hfirst _) (mul_mem (hfirst _) h2)
  apply top_unique
  intro z _
  change z ∈ S
  rw [quadratic_expansion z]
  exact add_mem (hsecond _) (mul_mem (hsecond _) h3)

theorem W_ne_rational (r : ℚ) : W ≠ algebraMap ℚ K r := by
  intro h
  apply W_transcendental
  rw [h]
  exact isAlgebraic_algebraMap r

theorem W_ne_zero : W ≠ 0 := by simpa using W_ne_rational 0

theorem qA_W_ne_zero : qA W ≠ 0 := by
  have hBeta : W ≠ (beta : K) := by
    rw [← map_beta (algebraMap ℚ K)]
    exact W_ne_rational (beta : ℚ)
  exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hBeta)

theorem qB_W_ne_zero : qB W ≠ 0 := by
  have hGamma : W ≠ (gamma : K) := by
    rw [← map_gamma (algebraMap ℚ K)]
    exact W_ne_rational (gamma : ℚ)
  exact mul_ne_zero (mul_ne_zero (by norm_num) beta_ne_zero) (sub_ne_zero.mpr hGamma)

/-- The generic fiber over the constructed Q(G₂) is elliptic. -/
instance genericFiberElliptic : (F W).IsElliptic := by
  have h1 : W ≠ 1 := by simpa using W_ne_rational 1
  have hLambda : W ≠ (lambda : K)^2 := by
    rw [← map_lambda (algebraMap ℚ K),← map_pow]
    exact W_ne_rational ((lambda : ℚ)^2)
  have hLambdaNeg : W ≠ -(lambda : K) := by
    rw [← map_lambda (algebraMap ℚ K),← map_neg]
    exact W_ne_rational (-(lambda : ℚ))
  have hplus : W+lambda ≠ 0 := by
    intro h
    apply hLambdaNeg
    linear_combination h
  have hV : V W ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr hLambda)
  constructor
  rw [isUnit_iff_ne_zero,F_discriminant,U_sq_sub_fourV_sq]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 hV))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 2 one_add_lambda_ne_zero)) W_ne_zero) (pow_ne_zero 2 hplus))

/-- The affine G₂ point in its constructed function field. -/
def genericBasePoint : G2Point K where
  W := W
  s1 := s1
  s2 := s2
  s3 := s3
  s1_sq := s1_sq
  s2_sq := s2_sq
  s3_sq := s3_sq

/-- The six printed points in the generic elliptic point group F(Q(G₂)).
This is equation membership and does not assert their independence. -/
def points : Fin 6 → (F W).toAffine.Point := by
  letI : (F genericBasePoint.W).IsElliptic := genericFiberElliptic
  exact genericBasePoint.sixPoints W_ne_zero qA_W_ne_zero qB_W_ne_zero

end
end Z2Z4Rank6.SecondFunctionField
