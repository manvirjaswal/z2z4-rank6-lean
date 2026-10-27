import Z2Z4Rank6.TwistCharacters
import Z2Z4Rank6.FunctionFieldCharacters
import Z2Z4Rank6.CharacterRationalization

/-!
# The four-twist rank decomposition

The arithmetic bridge for Remark 4.3 and the rank decomposition in Proposition
5.2 of Manvir Jaswal, "Infinitely many elliptic curves with torsion Z/2Z × Z/4Z
and rank at least six", DOI: 10.5281/zenodo.23437117.

The four twist point groups over Q(m) rationalize to the four character
spaces in the point group over Q(C).
-/

namespace Z2Z4Rank6.FunctionField.TwistCharacters

open scoped TensorProduct

noncomputable section

/-- The paper's model X^q, with its split cubic coefficients. -/
def paperTwist (q : Base) : WeierstrassCurve Base :=
  PointScaling.curve (q * A) (q ^ 2 * B)

theorem paperTwist_equation (q x y : Base) :
    (paperTwist q).toAffine.Equation x y ↔
      y ^ 2 = x * (x + q * (a RatFunc.X) ^ 2) * (x + q * (b RatFunc.X) ^ 2) := by
  rw [paperTwist, PointScaling.equation_iff]
  simp only [A, B]
  constructor <;> intro h <;> linear_combination h

theorem twistCurve_trivial : twistCurve (false, false) = X (RatFunc.X : Base) := by
  ext <;> simp [twistCurve, twistD, PointScaling.curve, A, B, X, E]

theorem twistCurve_q1 : twistCurve (true, false) = paperTwist (q1 (RatFunc.X ^ 2)) := rfl

theorem twistCurve_q2 : twistCurve (false, true) = paperTwist (q2 (RatFunc.X ^ 2)) := rfl

theorem twistCurve_q12 : twistCurve (true, true) = paperTwist (q12 (RatFunc.X ^ 2)) := by
  have hq : d1 * d2 / 25 = q12 (RatFunc.X ^ 2) := by
    rw [d1, d2, q1_mul_q2]
    field_simp
  change paperTwist (d1 * d2 / 25) = _
  rw [hq]

/-- The point group on the corresponding quadratic twist over Q(m). -/
abbrev twistPoints (χ : Bool × Bool) := (twistCurve χ).toAffine.Point

/-- The base twist group, tensored with Q, is its character space
inside E(Q(C)) tensor Q. Integral descent supplies the group equivalence, and
the four-term norm divided by four supplies the rationalized equivalence. -/
def rationalizedTwistCharacterEquiv (χ : Bool × Bool) :
    (ℚ ⊗[ℤ] twistPoints χ) ≃ₗ[ℚ] characterSpace χ :=
  (PointScaling.rationalizeEquiv (characterEquiv χ)).trans
    (CharacterRationalization.equivCharacterSpace
      pointSigmaU.toAddMonoidHom pointSigmaV.toAddMonoidHom
      pointSigmaU_involutive pointSigmaV_involutive pointSigmaU_pointSigmaV_commute χ)

/-- A canonical rational linear equivalence between E(Q(C)) tensor Q
and the product of the four base quadratic-twist rationalizations. -/
def fourTwistEquiv : RationalizedPoints ≃ₗ[ℚ] ∀ χ : Bool × Bool, ℚ ⊗[ℤ] twistPoints χ :=
  characterDecomposition.trans
    (LinearEquiv.piCongrRight fun χ => (rationalizedTwistCharacterEquiv χ).symm)

private theorem group_rank_eq_rationalized_rank (G : Type*) [AddCommGroup G] :
    Module.rank ℤ G = Module.rank ℚ (ℚ ⊗[ℤ] G) := by
  calc
    Module.rank ℤ G = Module.rank ℤ (ℚ ⊗[ℤ] G) :=
      (IsLocalizedModule.rank_eq (nonZeroDivisors ℤ) le_rfl
        (TensorProduct.mk ℤ ℚ G 1)).symm
    _ = Module.rank ℚ (ℚ ⊗[ℤ] G) :=
      (IsFractionRing.rank_right_eq ℤ ℚ (ℚ ⊗[ℤ] G)).symm

theorem twist_rank_eq_character_rank (χ : Bool × Bool) :
    Module.rank ℤ (twistPoints χ) = Module.rank ℚ (characterSpace χ) :=
  (group_rank_eq_rationalized_rank (twistPoints χ)).trans
    (rationalizedTwistCharacterEquiv χ).rank_eq

/-- The integral rank decomposition into the four base quadratic
twists. Cardinal ranks make this valid without finite-generation assumptions. -/
theorem pointGroup_rank_twist_decomposition : Module.rank ℤ PointGroup =
    Cardinal.sum (fun χ : Bool × Bool => Module.rank ℤ (twistPoints χ)) := by
  simpa only [← twist_rank_eq_character_rank] using pointGroup_rank_character_decomposition

theorem twist_finrank_eq_character_finrank (χ : Bool × Bool) :
    Module.finrank ℚ (ℚ ⊗[ℤ] twistPoints χ) = Module.finrank ℚ (characterSpace χ) :=
  (rationalizedTwistCharacterEquiv χ).finrank_eq

/-- The corresponding four-term dimension formula when the
function-field point group has finite-dimensional rationalization. -/
theorem pointGroup_finrank_four_twists [FiniteDimensional ℚ RationalizedPoints] :
    Module.finrank ℚ RationalizedPoints =
      Module.finrank ℚ (ℚ ⊗[ℤ] twistPoints (false, false)) +
      Module.finrank ℚ (ℚ ⊗[ℤ] twistPoints (true, false)) +
      Module.finrank ℚ (ℚ ⊗[ℤ] twistPoints (false, true)) +
      Module.finrank ℚ (ℚ ⊗[ℤ] twistPoints (true, true)) := by
  simpa only [← twist_finrank_eq_character_finrank] using character_finrank_four_spaces

end
end Z2Z4Rank6.FunctionField.TwistCharacters
