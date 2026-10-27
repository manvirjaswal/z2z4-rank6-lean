module

public import Z2Z4Rank6.SecondJDegree
public import Z2Z4Rank6.HeightInvariantForms

@[expose] public section

/-!
# Binary invariant forms for the second family in Remark 6.3

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3 and Theorem 8.1.
Coordinates are (x0,x1), W=x1/x0. The displayed integer equation has
coefficients Ubin,Vbin² and is obtained from F(W) by scaling x by
(1089*x0)². Its c4,c6 are homogeneous binary forms of degrees 4,6.
-/
namespace Z2Z4Rank6.SecondHeightInvariantForms
noncomputable section

/-- Integral homogenization of U, including the factor 1089². -/
def binaryU {R : Type*} [CommRing R] (x₀ x₁ : R) : R :=
  2*1450^2*x₁*x₀+2*(1089*x₁+361*x₀)^2

/-- Integral homogenization of V, with its printed sign. -/
def binaryV {R : Type*} [CommRing R] (x₀ x₁ : R) : R :=
  -(x₁-x₀)*(1185921*x₁-130321*x₀)

def model {R : Type*} [CommRing R] (u v : R) : WeierstrassCurve R where
  a₁:=0
  a₂:=u
  a₃:=0
  a₄:=v^2
  a₆:=0

def binaryModel {R : Type*} [CommRing R] (x₀ x₁ : R) : WeierstrassCurve R :=
  model (binaryU x₀ x₁) (binaryV x₀ x₁)

def c4 {R : Type*} [CommRing R] (x₀ x₁ : R) : R := (binaryModel x₀ x₁).c₄

def c6 {R : Type*} [CommRing R] (x₀ x₁ : R) : R := (binaryModel x₀ x₁).c₆

theorem model_c4 {R : Type*} [CommRing R] (u v : R) :
    (model u v).c₄=16*(u^2-3*v^2) := by
  simp only [model,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
  ring

theorem model_c6 {R : Type*} [CommRing R] (u v : R) :
    (model u v).c₆= -32*u*(2*u^2-9*v^2) := by
  simp only [model,WeierstrassCurve.c₆,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]
  ring

theorem model_discriminant {R : Type*} [CommRing R] (u v : R) :
    (model u v).Δ=16*v^4*(u^2-4*v^2) := by
  simp only [model,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem binaryU_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    binaryU (t*x₀) (t*x₁)=t^2*binaryU x₀ x₁ := by dsimp [binaryU]; ring

theorem binaryV_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    binaryV (t*x₀) (t*x₁)=t^2*binaryV x₀ x₁ := by dsimp [binaryV]; ring

theorem c4_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    c4 (t*x₀) (t*x₁)=t^4*c4 x₀ x₁ := by
  simp only [c4,binaryModel,model_c4,binaryU_scale,binaryV_scale]
  ring

theorem c6_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    c6 (t*x₀) (t*x₁)=t^6*c6 x₀ x₁ := by
  simp only [c6,binaryModel,model_c6,binaryU_scale,binaryV_scale]
  ring

theorem binaryU_affine {K : Type*} [Field K] [CharZero K] (x₀ x₁ : K) (hx : x₀≠0) :
    binaryU x₀ x₁=(1089*x₀)^2*SecondFamily.U (x₁/x₀) := by
  norm_num [binaryU,SecondFamily.U,SecondFamily.lambda]
  field_simp
  ring

theorem binaryV_affine {K : Type*} [Field K] [CharZero K] (x₀ x₁ : K) (hx : x₀≠0) :
    binaryV x₀ x₁=(1089*x₀)^2*SecondFamily.V (x₁/x₀) := by
  norm_num [binaryV,SecondFamily.V,SecondFamily.lambda]
  field_simp
  ring

/-- The displayed F family is the corresponding coefficient model. -/
theorem F_eq_model {K : Type*} [Field K] (w : K) :
    SecondFamily.F w=model (SecondFamily.U w) (SecondFamily.V w) := by
  ext <;> simp [SecondFamily.F,SecondFamily.twistedF,model]

/-- Admissible scaling of the coefficient model. -/
theorem scalingChange_model {K : Type*} [Field K] (r : Kˣ) (u v : K) :
    scalingChange r • model u v=model ((r:K)^2*u) ((r:K)^2*v) := by
  ext <;> simp [scalingChange,model,WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂,WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄,WeierstrassCurve.variableChange_a₆]
  ring

/-- The integer binary model is the printed F(x1/x0), scaled by
x↦(1089*x0)²x and y↦(1089*x0)³y. -/
theorem binaryModel_as_scaled {K : Type*} [Field K] [CharZero K] (x₀ x₁ : K) (hx : x₀≠0) :
    scalingChange (Units.mk0 (1089*x₀) (mul_ne_zero (by norm_num) hx)) •
      SecondFamily.F (x₁/x₀)=binaryModel x₀ x₁ := by
  rw [F_eq_model,scalingChange_model,binaryModel,binaryU_affine x₀ x₁ hx,binaryV_affine x₀ x₁ hx]
  rfl

/-- The checked rational U/V Bezout certificate evaluates over every char 0 field. -/
theorem U_V_not_both_zero {K : Type*} [Field K] [CharZero K] (w : K) :
    ¬(SecondFamily.U w=0 ∧ SecondFamily.V w=0) := by
  have h := SecondFamily.isCoprime_u_v_polynomial.map (Polynomial.eval₂RingHom (algebraMap ℚ K) w)
  have hcop : IsCoprime (SecondFamily.U w) (SecondFamily.V w) := by
    simpa [Polynomial.eval₂RingHom,SecondFamily.uPolynomial,SecondFamily.vPolynomial,
      SecondFamily.U,SecondFamily.V,SecondFamily.lambda,map_ofNat] using h
  rintro ⟨hu,hv⟩
  rw [hu,hv] at hcop
  exact not_isCoprime_zero_zero hcop

theorem binaryU_binaryV_not_both_zero {K : Type*} [Field K] [CharZero K]
    (x₀ x₁ : K) (hx : x₀≠0 ∨ x₁≠0) :
    ¬(binaryU x₀ x₁=0 ∧ binaryV x₀ x₁=0) := by
  by_cases h₀ : x₀=0
  · have h₁ : x₁≠0 := hx.resolve_left (not_not.mpr h₀)
    rintro ⟨_,hv⟩
    have he : binaryV x₀ x₁= -1185921*x₁^2 := by rw [h₀]; dsimp [binaryV]; ring
    rw [he] at hv
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 h₁)) hv
  · rintro ⟨hu,hv⟩
    apply U_V_not_both_zero (x₁/x₀)
    rw [binaryU_affine x₀ x₁ h₀] at hu
    rw [binaryV_affine x₀ x₁ h₀] at hv
    have hscale : (1089*x₀)^2≠0 := pow_ne_zero 2 (mul_ne_zero (by norm_num) h₀)
    exact ⟨(mul_eq_zero.mp hu).resolve_left hscale,(mul_eq_zero.mp hv).resolve_left hscale⟩

theorem model_invariants_zero {K : Type*} [Field K] [CharZero K] (u v : K)
    (h4 : (model u v).c₄=0) (h6 : (model u v).c₆=0) : u=0 ∧ v=0 := by
  have hΔ : (model u v).Δ=0 := by
    have h := (model u v).c_relation
    rw [h4,h6,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  rw [model_discriminant] at hΔ
  rw [model_c4] at h4
  have hbase : u^2-3*v^2=0 := (mul_eq_zero.mp h4).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hΔ with h | h
  · have hv : v=0 := (pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp
      ((mul_eq_zero.mp h).resolve_left (by norm_num))
    exact ⟨(pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa [hv] using hbase),hv⟩
  · have hd : u^2-4*v^2=0 := h
    have hv2 : v^2=0 := by linear_combination hbase-hd
    have hv : v=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hv2
    exact ⟨(pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa [hv] using hbase),hv⟩

/-- No common projective zero, including the point at infinity. -/
theorem invariants_not_both_zero {K : Type*} [Field K] [CharZero K]
    (x₀ x₁ : K) (hx : x₀≠0 ∨ x₁≠0) : ¬(c4 x₀ x₁=0 ∧ c6 x₀ x₁=0) := by
  rintro ⟨h4,h6⟩
  exact binaryU_binaryV_not_both_zero x₀ x₁ hx (model_invariants_zero _ _ h4 h6)

def UForm {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryU (MvPolynomial.X 0) (MvPolynomial.X 1)

def VForm {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryV (MvPolynomial.X 0) (MvPolynomial.X 1)

def c4Form {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R := (model UForm VForm).c₄

def c6Form {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R := (model UForm VForm).c₆

private def linearForm {R : Type*} [CommRing R] (a b : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C a*MvPolynomial.X 1+MvPolynomial.C b*MvPolynomial.X 0

private theorem linearForm_homogeneous {R : Type*} [CommRing R] (a b : R) :
    (linearForm a b).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X R 1).C_mul a).add
    ((MvPolynomial.isHomogeneous_X R 0).C_mul b)

theorem UForm_homogeneous {R : Type*} [CommRing R] : (UForm (R:=R)).IsHomogeneous 2 := by
  have h1 := ((MvPolynomial.isHomogeneous_X R (1:Fin 2)).mul
    (MvPolynomial.isHomogeneous_X R (0:Fin 2))).C_mul (2*1450^2:R)
  have h2 := ((linearForm_homogeneous (1089:R) 361).pow 2).C_mul (2:R)
  convert h1.add h2 using 1
  simp [UForm,binaryU,linearForm,map_ofNat,map_mul,map_pow]
  ring

theorem VForm_homogeneous {R : Type*} [CommRing R] : (VForm (R:=R)).IsHomogeneous 2 := by
  have h := ((linearForm_homogeneous (1:R) (-1)).mul
    (linearForm_homogeneous (1185921:R) (-130321))).C_mul (-1:R)
  convert h using 1
  simp [VForm,binaryV,linearForm,map_ofNat]
  ring

theorem c4Form_homogeneous {R : Type*} [CommRing R] : (c4Form (R:=R)).IsHomogeneous 4 := by
  rw [c4Form,model_c4]
  have h := ((UForm_homogeneous (R:=R)).pow 2).sub (((VForm_homogeneous (R:=R)).pow 2).C_mul 3)
  simpa [map_ofNat] using h.C_mul (16:R)

theorem c6Form_homogeneous {R : Type*} [CommRing R] : (c6Form (R:=R)).IsHomogeneous 6 := by
  rw [c6Form,model_c6]
  have h := (UForm_homogeneous (R:=R)).mul
    ((((UForm_homogeneous (R:=R)).pow 2).C_mul 2).sub
      (((VForm_homogeneous (R:=R)).pow 2).C_mul 9))
  simpa [map_ofNat,mul_assoc] using h.C_mul (-32:R)

@[simp] theorem eval_c4Form {R : Type*} [CommRing R] (x : Fin 2→R) :
    MvPolynomial.eval x c4Form=c4 (x 0) (x 1) := by
  simp [c4Form,c4,binaryModel,model_c4,UForm,VForm,binaryU,binaryV,map_ofNat]

@[simp] theorem eval_c6Form {R : Type*} [CommRing R] (x : Fin 2→R) :
    MvPolynomial.eval x c6Form=c6 (x 0) (x 1) := by
  simp [c6Form,c6,binaryModel,model_c6,UForm,VForm,binaryU,binaryV,map_ofNat]

theorem c4_at_infinity {R : Type*} [CommRing R] : c4 (0:R) 1=16*1089^4 := by
  norm_num [c4,binaryModel,model_c4,binaryU,binaryV]

theorem c6_at_infinity {R : Type*} [CommRing R] : c6 (0:R) 1=64*1089^6 := by
  norm_num [c6,binaryModel,model_c6,binaryU,binaryV]

theorem c4Form_totalDegree : (c4Form (R:=ℚ)).totalDegree=4 := by
  apply c4Form_homogeneous.totalDegree
  intro h
  have he := congrArg (MvPolynomial.eval ![(0:ℚ),1]) h
  norm_num [eval_c4Form,c4_at_infinity] at he

theorem c6Form_totalDegree : (c6Form (R:=ℚ)).totalDegree=6 := by
  apply c6Form_homogeneous.totalDegree
  intro h
  have he := congrArg (MvPolynomial.eval ![(0:ℚ),1]) h
  norm_num [eval_c6Form,c6_at_infinity] at he

theorem invariant_powers_homogeneous {R : Type*} [CommRing R] :
    ((c4Form (R:=R))^3).IsHomogeneous 12 ∧ ((c6Form (R:=R))^2).IsHomogeneous 12 :=
  ⟨c4Form_homogeneous.pow 3,c6Form_homogeneous.pow 2⟩

end
end Z2Z4Rank6.SecondHeightInvariantForms
