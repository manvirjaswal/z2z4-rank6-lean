module

public import Z2Z4Rank6.JDegree
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-!
# Binary invariant forms in Remark 6.3

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3.
The coordinates are ordered (x₀,x₁), so m=x₁/x₀ and x₀ is the
homogenizing coordinate. These are invariants of the displayed integral
binary model. No identification with the height of a minimal normalized
short Weierstrass equation or point-counting assertion is made here.
-/
namespace Z2Z4Rank6.HeightInvariantForms
noncomputable section

/-- Homogenized a, with denominator coordinate first. -/
def binaryA {R : Type*} [CommRing R] (x₀ x₁ : R) : R :=
  7*(x₁-99*x₀)*(x₁+x₀)*(x₁-11*x₀)*(x₁+9*x₀)

/-- Homogenized b, with the printed sign. -/
def binaryB {R : Type*} [CommRing R] (x₀ x₁ : R) : R :=
  -7*(x₁+99*x₀)*(x₁-x₀)*(x₁+11*x₀)*(x₁-9*x₀)

def binaryModel {R : Type*} [CommRing R] (x₀ x₁ : R) : WeierstrassCurve R :=
  E (binaryA x₀ x₁) (binaryB x₀ x₁)

def c4 {R : Type*} [CommRing R] (x₀ x₁ : R) : R := (binaryModel x₀ x₁).c₄

def c6 {R : Type*} [CommRing R] (x₀ x₁ : R) : R := (binaryModel x₀ x₁).c₆

theorem E_c4 {R : Type*} [CommRing R] (A B : R) :
    (E A B).c₄=16*(A^4-A^2*B^2+B^4) := by
  simp only [E,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
  ring

theorem E_c6 {R : Type*} [CommRing R] (A B : R) :
    (E A B).c₆= -32*(A^2+B^2)*(2*A^2-B^2)*(A^2-2*B^2) := by
  simp only [E,WeierstrassCurve.c₆,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]
  ring

theorem E_discriminant {R : Type*} [CommRing R] (A B : R) :
    (E A B).Δ=16*A^4*B^4*(A^2-B^2)^2 := by
  simp only [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem binaryA_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    binaryA (t*x₀) (t*x₁)=t^4*binaryA x₀ x₁ := by dsimp [binaryA]; ring

theorem binaryB_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    binaryB (t*x₀) (t*x₁)=t^4*binaryB x₀ x₁ := by dsimp [binaryB]; ring

theorem c4_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    c4 (t*x₀) (t*x₁)=t^16*c4 x₀ x₁ := by
  simp only [c4,binaryModel,E_c4,binaryA_scale,binaryB_scale]
  ring

theorem c6_scale {R : Type*} [CommRing R] (t x₀ x₁ : R) :
    c6 (t*x₀) (t*x₁)=t^24*c6 x₀ x₁ := by
  simp only [c6,binaryModel,E_c6,binaryA_scale,binaryB_scale]
  ring

theorem binaryA_affine {K : Type*} [Field K] (x₀ x₁ : K) (hx : x₀≠0) :
    binaryA x₀ x₁=x₀^4*a (x₁/x₀) := by
  dsimp [binaryA,a]
  field_simp

theorem binaryB_affine {K : Type*} [Field K] (x₀ x₁ : K) (hx : x₀≠0) :
    binaryB x₀ x₁=x₀^4*b (x₁/x₀) := by
  dsimp [binaryB,b]
  field_simp

/-- The polynomial Bezout identity remains valid in every char 0 field. -/
theorem a_b_not_both_zero {K : Type*} [Field K] [CharZero K] (m : K) :
    ¬(a m=0 ∧ b m=0) := by
  have h := isCoprime_a_b_poly.map (Polynomial.eval₂RingHom (algebraMap ℚ K) m)
  have hcop : IsCoprime (a m) (b m) := by
    simpa [Polynomial.eval₂RingHom,a,b,map_ofNat] using h
  rintro ⟨hA,hB⟩
  rw [hA,hB] at hcop
  exact not_isCoprime_zero_zero hcop

/-- This includes the projective point at infinity x₀=0. -/
theorem binaryA_binaryB_not_both_zero {K : Type*} [Field K] [CharZero K]
    (x₀ x₁ : K) (hx : x₀≠0 ∨ x₁≠0) :
    ¬(binaryA x₀ x₁=0 ∧ binaryB x₀ x₁=0) := by
  by_cases h₀ : x₀=0
  · have h₁ : x₁≠0 := hx.resolve_left (not_not.mpr h₀)
    rintro ⟨hA,_⟩
    have he : binaryA x₀ x₁=7*x₁^4 := by rw [h₀]; dsimp [binaryA]; ring
    rw [he] at hA
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 4 h₁)) hA
  · rintro ⟨hA,hB⟩
    apply a_b_not_both_zero (x₁/x₀)
    rw [binaryA_affine x₀ x₁ h₀] at hA
    rw [binaryB_affine x₀ x₁ h₀] at hB
    exact ⟨(mul_eq_zero.mp hA).resolve_left (pow_ne_zero 4 h₀),
      (mul_eq_zero.mp hB).resolve_left (pow_ne_zero 4 h₀)⟩

/-- Vanishing of both invariants forces both split root parameters to vanish. -/
theorem E_invariants_zero {K : Type*} [Field K] [CharZero K] (A B : K)
    (h4 : (E A B).c₄=0) (h6 : (E A B).c₆=0) : A=0 ∧ B=0 := by
  have hΔ : (E A B).Δ=0 := by
    have h := (E A B).c_relation
    rw [h4,h6,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  rw [E_discriminant] at hΔ
  rw [E_c4] at h4
  have hz : A=0 ∨ B=0 ∨ A^2=B^2 := by
    rcases mul_eq_zero.mp hΔ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl ((pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp ((mul_eq_zero.mp h).resolve_left (by norm_num)))
      · exact Or.inr (Or.inl ((pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h)))
  rcases hz with hA | hB | hab
  · subst A
    have hB : B^4=0 := by
      simpa using (mul_eq_zero.mp h4).resolve_left (by norm_num)
    exact ⟨rfl,(pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp hB⟩
  · subst B
    have hA : A^4=0 := by
      simpa using (mul_eq_zero.mp h4).resolve_left (by norm_num)
    exact ⟨(pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp hA,rfl⟩
  · have hA : A^4=0 := by
      have he : A^4-A^2*B^2+B^4=A^4 := by
        calc
          _ = (A^2)^2-A^2*B^2+(B^2)^2 := by ring
          _ = A^4 := by rw [←hab]; ring
      rw [he] at h4
      exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
    have hAz : A=0 := (pow_eq_zero_iff (by decide : (4:ℕ)≠0)).mp hA
    have hBz : B=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa [hAz] using hab.symm)
    exact ⟨hAz,hBz⟩

/-- The invariants have no common projective zero in characteristic 0. -/
theorem invariants_not_both_zero {K : Type*} [Field K] [CharZero K]
    (x₀ x₁ : K) (hx : x₀≠0 ∨ x₁≠0) : ¬(c4 x₀ x₁=0 ∧ c6 x₀ x₁=0) := by
  rintro ⟨h4,h6⟩
  exact binaryA_binaryB_not_both_zero x₀ x₁ hx
    (E_invariants_zero _ _ h4 h6)

/-- Binary multivariate polynomials, with index 0=x₀ and index 1=x₁. -/
def AForm {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryA (MvPolynomial.X 0) (MvPolynomial.X 1)

def BForm {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R :=
  binaryB (MvPolynomial.X 0) (MvPolynomial.X 1)

def c4Form {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R := (E AForm BForm).c₄

def c6Form {R : Type*} [CommRing R] : MvPolynomial (Fin 2) R := (E AForm BForm).c₆

private def linearForm {R : Type*} [CommRing R] (r : R) : MvPolynomial (Fin 2) R :=
  MvPolynomial.X 1+MvPolynomial.C r*MvPolynomial.X 0

private theorem linearForm_homogeneous {R : Type*} [CommRing R] (r : R) :
    (linearForm r).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_X R 1).add ((MvPolynomial.isHomogeneous_X R 0).C_mul r)

theorem AForm_homogeneous {R : Type*} [CommRing R] :
    (AForm (R:=R)).IsHomogeneous 4 := by
  have h := (((linearForm_homogeneous (-99:R)).mul (linearForm_homogeneous (1:R))).mul
    (linearForm_homogeneous (-11:R))).mul (linearForm_homogeneous (9:R))
  convert h.C_mul (7:R) using 1
  simp [AForm,binaryA,linearForm,map_ofNat]
  ring

theorem BForm_homogeneous {R : Type*} [CommRing R] :
    (BForm (R:=R)).IsHomogeneous 4 := by
  have h := (((linearForm_homogeneous (99:R)).mul (linearForm_homogeneous (-1:R))).mul
    (linearForm_homogeneous (11:R))).mul (linearForm_homogeneous (-9:R))
  convert h.C_mul (-7:R) using 1
  simp [BForm,binaryB,linearForm,map_ofNat]
  ring

theorem c4Form_homogeneous {R : Type*} [CommRing R] :
    (c4Form (R:=R)).IsHomogeneous 16 := by
  rw [c4Form,E_c4]
  have h := ((AForm_homogeneous (R:=R)).pow 4).sub
    (((AForm_homogeneous (R:=R)).pow 2).mul ((BForm_homogeneous (R:=R)).pow 2))
  have h' := h.add ((BForm_homogeneous (R:=R)).pow 4)
  simpa [map_ofNat] using h'.C_mul (16:R)

theorem c6Form_homogeneous {R : Type*} [CommRing R] :
    (c6Form (R:=R)).IsHomogeneous 24 := by
  rw [c6Form,E_c6]
  have hA := (AForm_homogeneous (R:=R)).pow 2
  have hB := (BForm_homogeneous (R:=R)).pow 2
  have h := ((hA.add hB).mul ((hA.C_mul (2:R)).sub hB)).mul
    (hA.sub (hB.C_mul (2:R)))
  simpa [mul_assoc,map_ofNat] using h.C_mul (-32:R)

@[simp] theorem eval_c4Form {R : Type*} [CommRing R] (x : Fin 2→R) :
    MvPolynomial.eval x c4Form=c4 (x 0) (x 1) := by
  simp [c4Form,c4,binaryModel,E_c4,AForm,BForm,binaryA,binaryB,map_ofNat]

@[simp] theorem eval_c6Form {R : Type*} [CommRing R] (x : Fin 2→R) :
    MvPolynomial.eval x c6Form=c6 (x 0) (x 1) := by
  simp [c6Form,c6,binaryModel,E_c6,AForm,BForm,binaryA,binaryB,map_ofNat]

theorem c4_at_infinity {R : Type*} [CommRing R] : c4 (0:R) 1=16*7^4 := by
  norm_num [c4,binaryModel,E_c4,binaryA,binaryB]

theorem c6_at_infinity {R : Type*} [CommRing R] : c6 (0:R) 1=64*7^6 := by
  norm_num [c6,binaryModel,E_c6,binaryA,binaryB]

theorem c4Form_totalDegree : (c4Form (R:=ℚ)).totalDegree=16 := by
  apply c4Form_homogeneous.totalDegree
  intro h
  have he := congrArg (MvPolynomial.eval ![(0:ℚ),1]) h
  norm_num [eval_c4Form,c4_at_infinity] at he

theorem c6Form_totalDegree : (c6Form (R:=ℚ)).totalDegree=24 := by
  apply c6Form_homogeneous.totalDegree
  intro h
  have he := congrArg (MvPolynomial.eval ![(0:ℚ),1]) h
  norm_num [eval_c6Form,c6_at_infinity] at he

/-- The two degree 48 invariant powers used in the raw height. -/
theorem invariant_powers_homogeneous {R : Type*} [CommRing R] :
    ((c4Form (R:=R))^3).IsHomogeneous 48 ∧
      ((c6Form (R:=R))^2).IsHomogeneous 48 := by
  exact ⟨c4Form_homogeneous.pow 3,c6Form_homogeneous.pow 2⟩

end
end Z2Z4Rank6.HeightInvariantForms
