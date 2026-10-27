import Z2Z4Rank6.SecondFunctionFieldPointActions
import Z2Z4Rank6.BiquadraticDecomposition

/-! The four character spaces used in the printed proof of
Theorem 8.1(b), and independence after separating its four blocks. -/

namespace Z2Z4Rank6.SecondFunctionField
noncomputable section
open scoped TensorProduct DirectSum
set_option maxRecDepth 3000

abbrev RationalizedPoints := ℚ ⊗[ℤ] PointGroup

def linearSigma2 : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointSigma2.toAddMonoidHom

def linearSigma3 : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointSigma3.toAddMonoidHom

theorem linearSigma2_involutive : linearSigma2.comp linearSigma2=LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ pointSigma2_involutive

theorem linearSigma3_involutive : linearSigma3.comp linearSigma3=LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ pointSigma3_involutive

theorem linearSigma2_linearSigma3_commute :
    linearSigma2.comp linearSigma3=linearSigma3.comp linearSigma2 :=
  PointScaling.rationalizeHom_commute _ _ pointSigma2_pointSigma3_commute

def characterSpace (χ : Bool × Bool) : Submodule ℚ RationalizedPoints :=
  Biquadratic.jointSpace linearSigma2 linearSigma3 χ

def rationalPoints (j : Fin 6) : RationalizedPoints := (1 : ℚ) ⊗ₜ[ℤ] points j

theorem rationalPoints_mem_characterSpace (j : Fin 6) :
    rationalPoints j ∈ characterSpace (pointCharacter j) := by
  rw [characterSpace,Biquadratic.mem_jointSpace]
  constructor
  · change (1 : ℚ) ⊗ₜ[ℤ] pointSigma2 (points j)=_
    rw [pointSigma2_points]
    cases h : (pointCharacter j).1 <;>
      simp [Biquadratic.characterSign,rationalPoints,TensorProduct.tmul_neg]
  · change (1 : ℚ) ⊗ₜ[ℤ] pointSigma3 (points j)=_
    rw [pointSigma3_points]
    cases h : (pointCharacter j).2 <;>
      simp [Biquadratic.characterSign,rationalPoints,TensorProduct.tmul_neg]

def characterDecomposition : RationalizedPoints ≃ₗ[ℚ]
    ∀ χ : Bool × Bool,characterSpace χ :=
  Biquadratic.decompositionEquiv linearSigma2 linearSigma3
    linearSigma2_involutive linearSigma3_involutive linearSigma2_linearSigma3_commute

def characterDirectSum : RationalizedPoints ≃ₗ[ℚ]
    ⨁ χ : Bool × Bool,characterSpace χ :=
  Biquadratic.directSumEquiv linearSigma2 linearSigma3
    linearSigma2_involutive linearSigma3_involutive linearSigma2_linearSigma3_commute

theorem rationalPoints_projector (χ : Bool × Bool) (j : Fin 6) :
    Biquadratic.projector linearSigma2 linearSigma3 χ (rationalPoints j)=
      if χ=pointCharacter j then rationalPoints j else 0 :=
  Biquadratic.projector_on_jointSpace _ _ _ _ _ (rationalPoints_mem_characterSpace j)

/-- The character argument itself needs just the four block
independence assertions; the later specialization module supplies them. -/
theorem rationalPoints_independent_of_blocks
    (h0 : LinearIndependent ℤ ![points 0])
    (hA : LinearIndependent ℤ ![points 1,points 2])
    (hB : LinearIndependent ℤ ![points 3,points 4])
    (hH : LinearIndependent ℤ ![points 5]) :
    LinearIndependent ℚ rationalPoints := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have h0Q := Module.Flat.linearIndependent_one_tmul (S:=ℚ) h0
  have hAQ := Module.Flat.linearIndependent_one_tmul (S:=ℚ) hA
  have hBQ := Module.Flat.linearIndependent_one_tmul (S:=ℚ) hB
  have hHQ := Module.Flat.linearIndependent_one_tmul (S:=ℚ) hH
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hp (χ : Bool × Bool) := congrArg (Biquadratic.projector linearSigma2 linearSigma3 χ) hn
  simp only [map_sum,map_smul,map_zero,rationalPoints_projector] at hp
  have hc0 : n 0=0 := by
    have hh := Fintype.linearIndependent_iff.mp h0Q ![n 0] (by
      simpa [pointCharacter,rationalPoints,Fin.sum_univ_succ] using hp (false,false))
    exact hh 0
  have hcA : ∀ i : Fin 2,(![n 1,n 2] : Fin 2 → ℚ) i=0 :=
    Fintype.linearIndependent_iff.mp hAQ ![n 1,n 2] (by
      simpa [pointCharacter,rationalPoints,Fin.sum_univ_succ] using hp (true,false))
  have hcB : ∀ i : Fin 2,(![n 3,n 4] : Fin 2 → ℚ) i=0 :=
    Fintype.linearIndependent_iff.mp hBQ ![n 3,n 4] (by
      simpa [pointCharacter,rationalPoints,Fin.sum_univ_succ] using hp (false,true))
  have hcH : n 5=0 := by
    have hh := Fintype.linearIndependent_iff.mp hHQ ![n 5] (by
      simpa [pointCharacter,rationalPoints,Fin.sum_univ_succ] using hp (true,true))
    exact hh 0
  intro i
  fin_cases i
  · exact hc0
  · exact hcA 0
  · exact hcA 1
  · exact hcB 0
  · exact hcB 1
  · exact hcH

theorem points_independent_of_blocks
    (h0 : LinearIndependent ℤ ![points 0])
    (hA : LinearIndependent ℤ ![points 1,points 2])
    (hB : LinearIndependent ℤ ![points 3,points 4])
    (hH : LinearIndependent ℤ ![points 5]) :
    LinearIndependent ℤ points := by
  have hQ := rationalPoints_independent_of_blocks h0 hA hB hH
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hsum : ∑ i : Fin 6,(n i : ℚ) • rationalPoints i=0 := by
    have h := congrArg (fun P : PointGroup=>(1 : ℚ) ⊗ₜ[ℤ] P) hn
    simpa [rationalPoints,TensorProduct.tmul_sum,Int.cast_smul_eq_zsmul] using h
  have hz := Fintype.linearIndependent_iff.mp hQ (fun i=>(n i : ℚ)) hsum
  intro i
  exact_mod_cast hz i

end
end Z2Z4Rank6.SecondFunctionField
