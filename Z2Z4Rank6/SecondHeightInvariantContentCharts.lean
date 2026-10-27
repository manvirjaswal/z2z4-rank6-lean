module

public import Z2Z4Rank6.SecondHeightInvariantForms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

/-! The degree 12 short-invariant forms and their two coprime affine
charts, for the integral-content step of Jaswal Remark 6.3,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.SecondHeightInvariantContent
noncomputable section
open scoped Classical
open SecondHeightInvariantForms

abbrev BinaryForm := MvPolynomial (Fin 2) ℤ

def shortC4Cube : BinaryForm := (-27*c4Form)^3

def shortC6Square : BinaryForm := (-54*c6Form)^2

def swapVariables (F : BinaryForm) : BinaryForm :=
  MvPolynomial.rename (Equiv.swap (0:Fin 2) 1) F

theorem shortC4Cube_homogeneous : shortC4Cube.IsHomogeneous 12 := by
  have h := (c4Form_homogeneous (R:=ℤ)).C_mul (-27)
  simpa [shortC4Cube,map_ofNat] using h.pow 3

theorem shortC6Square_homogeneous : shortC6Square.IsHomogeneous 12 := by
  have h := (c6Form_homogeneous (R:=ℤ)).C_mul (-54)
  simpa [shortC6Square,map_ofNat] using h.pow 2

theorem swapVariables_homogeneous (F : BinaryForm) (D : ℕ) (hF : F.IsHomogeneous D) :
    (swapVariables F).IsHomogeneous D := hF.rename_isHomogeneous

/-- Double evaluation of the integer affine chart is the field
coordinate evaluation; rational coefficient maps are fixed by casts. -/
theorem map_aeval_chart {K : Type*} [Field K] [Algebra ℚ K]
    (F : BinaryForm) (z : K) :
    Polynomial.aeval z ((MvPolynomial.aeval ![Polynomial.X,1] F).map (algebraMap ℤ ℚ))=
      MvPolynomial.eval₂ (Int.castRingHom K) ![z,1] F := by
  have hhom :
      (Polynomial.aeval z).toRingHom.comp ((Polynomial.mapRingHom (algebraMap ℤ ℚ)).comp
        (MvPolynomial.aeval ![Polynomial.X,1]).toRingHom)=
      MvPolynomial.eval₂Hom (Int.castRingHom K) ![z,1] := by
    apply MvPolynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun hhom F

@[simp] theorem eval₂_shortC4Cube {K : Type*} [CommRing K] (x : Fin 2→K) :
    MvPolynomial.eval₂ (Int.castRingHom K) x shortC4Cube=(-27*c4 (x 0) (x 1))^3 := by
  simp [shortC4Cube,c4Form,c4,binaryModel,model_c4,UForm,VForm,binaryU,binaryV]

@[simp] theorem eval₂_shortC6Square {K : Type*} [CommRing K] (x : Fin 2→K) :
    MvPolynomial.eval₂ (Int.castRingHom K) x shortC6Square=(-54*c6 (x 0) (x 1))^2 := by
  simp [shortC6Square,c6Form,c6,binaryModel,model_c6,UForm,VForm,binaryU,binaryV]

theorem eval₂_swapVariables {K : Type*} [CommRing K] (F : BinaryForm) (x₀ x₁ : K) :
    MvPolynomial.eval₂ (Int.castRingHom K) ![x₀,x₁] (swapVariables F)=
      MvPolynomial.eval₂ (Int.castRingHom K) ![x₁,x₀] F := by
  rw [swapVariables,MvPolynomial.eval₂_rename]
  congr 1
  funext i
  fin_cases i <;> simp

@[simp] theorem eval_shortC4Cube (x : Fin 2→ℤ) :
    MvPolynomial.eval x shortC4Cube=(-27*c4 (x 0) (x 1))^3 := by
  simp [shortC4Cube,c4Form,c4,binaryModel,model_c4,UForm,VForm,binaryU,binaryV]

@[simp] theorem eval_shortC6Square (x : Fin 2→ℤ) :
    MvPolynomial.eval x shortC6Square=(-54*c6 (x 0) (x 1))^2 := by
  simp [shortC6Square,c6Form,c6,binaryModel,model_c6,UForm,VForm,binaryU,binaryV]

theorem eval_swapVariables (F : BinaryForm) (x₀ x₁ : ℤ) :
    MvPolynomial.eval ![x₀,x₁] (swapVariables F)=MvPolynomial.eval ![x₁,x₀] F := by
  have hvec : (![x₀,x₁] ∘ Equiv.swap (0:Fin 2) 1)=![x₁,x₀] := by
    funext i
    fin_cases i <;> simp
  rw [swapVariables,MvPolynomial.eval_rename,hvec]

/-- The normalization powers have no common zero on either chart. -/
theorem short_invariants_not_both_zero {K : Type*} [Field K] [CharZero K]
    (x₀ x₁ : K) (hx : x₀≠0 ∨ x₁≠0) :
    ¬((-27*c4 x₀ x₁)^3=0 ∧ (-54*c6 x₀ x₁)^2=0) := by
  rintro ⟨h4,h6⟩
  apply invariants_not_both_zero x₀ x₁ hx
  have h4' := (pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp h4
  have h6' := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h6
  exact ⟨(mul_eq_zero.mp h4').resolve_left (by norm_num),
    (mul_eq_zero.mp h6').resolve_left (by norm_num)⟩

theorem short_chart_coprime :
    IsCoprime ((MvPolynomial.aeval ![Polynomial.X,1] shortC4Cube).map (algebraMap ℤ ℚ))
      ((MvPolynomial.aeval ![Polynomial.X,1] shortC6Square).map (algebraMap ℤ ℚ)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ (AlgebraicClosure ℚ) _ _).mpr
  intro z
  rw [map_aeval_chart,map_aeval_chart,eval₂_shortC4Cube,eval₂_shortC6Square]
  exact not_and_or.mp (short_invariants_not_both_zero z 1 (Or.inr one_ne_zero))

theorem short_swapped_chart_coprime :
    IsCoprime ((MvPolynomial.aeval ![Polynomial.X,1] (swapVariables shortC4Cube)).map (algebraMap ℤ ℚ))
      ((MvPolynomial.aeval ![Polynomial.X,1] (swapVariables shortC6Square)).map (algebraMap ℤ ℚ)) := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℚ (AlgebraicClosure ℚ) _ _).mpr
  intro z
  rw [map_aeval_chart,map_aeval_chart,eval₂_swapVariables,eval₂_swapVariables,
    eval₂_shortC4Cube,eval₂_shortC6Square]
  exact not_and_or.mp (short_invariants_not_both_zero 1 z (Or.inl one_ne_zero))

end
end Z2Z4Rank6.SecondHeightInvariantContent
