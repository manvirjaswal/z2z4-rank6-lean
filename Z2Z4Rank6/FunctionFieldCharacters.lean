module

public import Z2Z4Rank6.FunctionFieldPointActions
public import Z2Z4Rank6.PointScaling
public import Z2Z4Rank6.BiquadraticDecomposition
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

/-!
# The four character spaces of X(Q(C)) tensor Q

This instantiates Remark 4.3 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117, on the constructed function field and
elliptic point group. The two rational linear actions arise from the
proved field and point-group sign involutions. Identifying each character
space with the corresponding twist is a separate descent step.
-/

namespace Z2Z4Rank6.FunctionField

open scoped TensorProduct DirectSum

noncomputable section

/-- The rationalization of the elliptic point group X(Q(C)). -/
abbrev RationalizedPoints := ℚ ⊗[ℤ] PointGroup

/-- Rational linear action induced by the u-sign point automorphism. -/
def linearSigmaU : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointSigmaU.toAddMonoidHom

/-- Rational linear action induced by the v-sign point automorphism. -/
def linearSigmaV : RationalizedPoints →ₗ[ℚ] RationalizedPoints :=
  PointScaling.rationalizeHom pointSigmaV.toAddMonoidHom

/-- The first rational linear action is an involution. -/
theorem linearSigmaU_involutive : linearSigmaU.comp linearSigmaU = LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ (fun P => pointSigmaU_involutive P)

/-- The second rational linear action is an involution. -/
theorem linearSigmaV_involutive : linearSigmaV.comp linearSigmaV = LinearMap.id :=
  PointScaling.rationalizeHom_involutive _ (fun P => pointSigmaV_involutive P)

/-- The two rational linear sign actions commute. -/
theorem linearSigmaU_linearSigmaV_commute :
    linearSigmaU.comp linearSigmaV = linearSigmaV.comp linearSigmaU :=
  PointScaling.rationalizeHom_commute _ _ (fun P => pointSigmaU_pointSigmaV_commute P)

/-- The joint character space in X(Q(C)) tensor Q; false is positive
and true is negative for the u and v actions, respectively. -/
def characterSpace (χ : Bool × Bool) : Submodule ℚ RationalizedPoints :=
  Biquadratic.jointSpace linearSigmaU linearSigmaV χ

/-- The six printed points, mapped to the rationalized point group. -/
def rationalPoints (j : Fin 6) : RationalizedPoints := (1 : ℚ) ⊗ₜ[ℤ] points j

/-- The u-character of each printed point is its printed sign under u↦-u. -/
theorem linearSigmaU_rationalPoints (j : Fin 6) :
    linearSigmaU (rationalPoints j) =
      Biquadratic.characterSign (pointCharacter j).1 • rationalPoints j := by
  change (1 : ℚ) ⊗ₜ[ℤ] pointSigmaU (points j) = _
  rw [pointSigmaU_points]
  cases h : (pointCharacter j).1 <;> simp [Biquadratic.characterSign, rationalPoints, TensorProduct.tmul_neg]

/-- The v-character of each printed point is its printed sign under v↦-v. -/
theorem linearSigmaV_rationalPoints (j : Fin 6) :
    linearSigmaV (rationalPoints j) =
      Biquadratic.characterSign (pointCharacter j).2 • rationalPoints j := by
  change (1 : ℚ) ⊗ₜ[ℤ] pointSigmaV (points j) = _
  rw [pointSigmaV_points]
  cases h : (pointCharacter j).2 <;> simp [Biquadratic.characterSign, rationalPoints, TensorProduct.tmul_neg]

/-- P1,P2,P3 lie in the positive-positive space, P4 in the v-negative
space, P5 in the u-negative space, and P6 in the negative-negative space. -/
theorem rationalPoints_mem_characterSpace (j : Fin 6) :
    rationalPoints j ∈ characterSpace (pointCharacter j) := by
  rw [characterSpace, Biquadratic.mem_jointSpace]
  exact ⟨linearSigmaU_rationalPoints j,linearSigmaV_rationalPoints j⟩

/-- The rationalized point group decomposes as the four
character spaces of the two sign actions. -/
def characterDecomposition : RationalizedPoints ≃ₗ[ℚ] ∀ χ : Bool × Bool, characterSpace χ :=
  Biquadratic.decompositionEquiv linearSigmaU linearSigmaV
    linearSigmaU_involutive linearSigmaV_involutive linearSigmaU_linearSigmaV_commute

/-- The same decomposition, expressed as an external direct sum. -/
def characterDirectSum : RationalizedPoints ≃ₗ[ℚ] ⨁ χ : Bool × Bool, characterSpace χ :=
  Biquadratic.directSumEquiv linearSigmaU linearSigmaV
    linearSigmaU_involutive linearSigmaV_involutive linearSigmaU_linearSigmaV_commute

/-- Cardinal ranks of the four character spaces add to the
rank of the rationalized point group. -/
theorem character_rank_decomposition : Module.rank ℚ RationalizedPoints =
    Cardinal.sum (fun χ : Bool × Bool => Module.rank ℚ (characterSpace χ)) :=
  Biquadratic.rank_decomposition linearSigmaU linearSigmaV
    linearSigmaU_involutive linearSigmaV_involutive linearSigmaU_linearSigmaV_commute

/-- Localization kills torsion while preserving module rank: the integral
rank of the point group equals the dimension of its rationalization. -/
theorem pointGroup_rank_eq_rationalized_rank :
    Module.rank ℤ PointGroup = Module.rank ℚ RationalizedPoints := by
  calc
    Module.rank ℤ PointGroup = Module.rank ℤ RationalizedPoints :=
      (IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl
        (TensorProduct.mk ℤ ℚ PointGroup 1)).symm
    _ = Module.rank ℚ RationalizedPoints :=
      (IsFractionRing.rank_right_eq ℤ ℚ RationalizedPoints).symm

/-- Integral independence of the six points survives rationalization. -/
theorem rationalPoints_linearIndependent_of_points
    (h : LinearIndependent ℤ points) : LinearIndependent ℚ rationalPoints := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact Module.Flat.linearIndependent_one_tmul h

/-- The integral group rank is the sum of the four character
ranks. This assertion does not assume that the point group is finitely generated. -/
theorem pointGroup_rank_character_decomposition : Module.rank ℤ PointGroup =
    Cardinal.sum (fun χ : Bool × Bool => Module.rank ℚ (characterSpace χ)) :=
  pointGroup_rank_eq_rationalized_rank.trans character_rank_decomposition

/-- Under finite-dimensionality, the four character dimensions add to
the dimension of the rationalized point group. -/
theorem character_finrank_four_spaces [FiniteDimensional ℚ RationalizedPoints] :
    Module.finrank ℚ RationalizedPoints =
      Module.finrank ℚ (characterSpace (false,false)) +
      Module.finrank ℚ (characterSpace (true,false)) +
      Module.finrank ℚ (characterSpace (false,true)) +
      Module.finrank ℚ (characterSpace (true,true)) :=
  Biquadratic.finrank_four_spaces linearSigmaU linearSigmaV
    linearSigmaU_involutive linearSigmaV_involutive linearSigmaU_linearSigmaV_commute

end
end Z2Z4Rank6.FunctionField
