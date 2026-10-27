module

public import Z2Z4Rank6.NeronRigidCounting
public import Z2Z4Rank6.SecondPointPlaceEquiv
public import Z2Z4Rank6.SecondBaseMathlibFunctionFieldIso
public import Z2Z4Rank6.SecondJacobianExactRank
public import Z2Z4Rank6.CountingExponentAddition

@[expose] public section

/-!
# Second-base counts by reduced W-height

Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117. The degree-eight
field is identified with Mathlib's printed elliptic function field, and
all normalized rational places are proved equivalent to the unramified
G₂ points. Their count has exponent 1 by Néron's generic theorem and the
proved rank 2. The finite branch fibers are then restored by a
proved finite-addition argument.
-/

namespace Z2Z4Rank6.SecondParameterCounting
open SecondFamily
open scoped Classical
noncomputable section

abbrev Point := SecondFunctionFieldPointPlace.Point

local instance secondCountingScalarTower :
    @IsScalarTower ℚ (RatFunc ℚ) SecondFunctionField.K
      (inferInstance : SMul ℚ (RatFunc ℚ))
      (Algebra.toSMul : SMul (RatFunc ℚ) SecondFunctionField.K)
      (Algebra.toSMul : SMul ℚ SecondFunctionField.K) := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=RatFunc ℚ) (A:=SecondFunctionField.K)
    (Subsingleton.elim _ _)

local instance secondCountingFiniteDimensional :
    FiniteDimensional (RatFunc ℚ) SecondFunctionField.K :=
  Module.Finite.of_basis SecondFunctionField.basis

def pointHeightSet (H : ℕ) : Set Point := {P | rationalParameterHeight P.val.W≤H}
def pointCount (H : ℕ) : ℕ := (pointHeightSet H).ncard

theorem place_image_heightSet (H : ℕ) :
    SecondPointPlaceEquiv.equiv '' pointHeightSet H=rigidPlaceHeightSet SecondFunctionField.K H := by
  ext v
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact hP
  · intro hv
    refine ⟨SecondPointPlaceEquiv.equiv.symm v,?_,SecondPointPlaceEquiv.equiv.apply_symm_apply v⟩
    exact hv

theorem pointCount_eq_rigidPlaceCount (H : ℕ) :
    pointCount H=rigidPlaceCount SecondFunctionField.K H := by
  rw [pointCount,rigidPlaceCount,←place_image_heightSet]
  exact (Set.ncard_image_of_injective _ SecondPointPlaceEquiv.equiv.injective).symm

theorem point_counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀ H,(pointHeightSet H).Finite) ∧ HasLogarithmicCountingExponent pointCount 1 := by
  obtain ⟨hFinite,hCount⟩ := rigid_place_counting hN SecondFunctionField.K J2
    SecondBaseMathlibFunctionFieldIso.secondFunctionFieldEquivMathlib 2 (by decide)
    (secondJacobian_rank_eq_two hMW hMazur hDescent)
  refine ⟨fun H => ((place_image_heightSet H).symm ▸ hFinite H).of_finite_image
    SecondPointPlaceEquiv.equiv.injective.injOn,?_⟩
  have he : rigidPlaceCount SecondFunctionField.K=pointCount :=
    funext (fun H => (pointCount_eq_rigidPlaceCount H).symm)
  rw [he] at hCount
  norm_num only [Nat.cast_ofNat,show (2:ℝ)/2=1 by norm_num] at hCount
  exact hCount

def parameterHeight (P : G2Point ℚ) : ℕ := rationalParameterHeight P.W
def heightSet (H : ℕ) : Set (G2Point ℚ) := BoundedHeightCounting.boundedSet parameterHeight H
def count (H : ℕ) : ℕ := BoundedHeightCounting.count parameterHeight H

theorem point_image_heightSet (H : ℕ) :
    Subtype.val '' pointHeightSet H=heightSet H∩SecondFunctionFieldPointPlace.branchPointsᶜ := by
  ext P
  constructor
  · rintro ⟨p,hp,rfl⟩
    refine ⟨hp,?_⟩
    change ¬(p.val.W=0 ∨ p.val.W=(beta:ℚ) ∨ p.val.W=(gamma:ℚ))
    have hn := p.property
    tauto
  · intro hP
    have hn : P.W≠0 ∧ P.W≠(beta:ℚ) ∧ P.W≠(gamma:ℚ) := by
      have hnot := hP.2
      change ¬(P.W=0 ∨ P.W=(beta:ℚ) ∨ P.W=(gamma:ℚ)) at hnot
      tauto
    exact ⟨⟨P,hn⟩,hP.1,rfl⟩

theorem restrictedCount_eq (H : ℕ) :
    BoundedHeightCounting.restrictedCount parameterHeight
      SecondFunctionFieldPointPlace.branchPointsᶜ H=pointCount H := by
  change (heightSet H∩SecondFunctionFieldPointPlace.branchPointsᶜ).ncard=pointCount H
  rw [←point_image_heightSet,pointCount]
  exact Set.ncard_image_of_injective _ Subtype.val_injective

/-- Every G₂-point set with bounded reduced W-height is finite,
and its full count is (log H)^(1+o(1)). -/
theorem counting (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀ H,(heightSet H).Finite) ∧ HasLogarithmicCountingExponent count 1 := by
  obtain ⟨hFinite,hCount⟩ := point_counting hN hMW hMazur hDescent
  apply BoundedHeightCounting.counting_of_cofinite_restriction
    (S:=SecondFunctionFieldPointPlace.branchPointsᶜ) ?_ ?_ (by norm_num)
    (by simpa only [compl_compl] using SecondFunctionFieldPointPlace.branchPoints_finite)
  · intro H
    change (heightSet H∩SecondFunctionFieldPointPlace.branchPointsᶜ).Finite
    rw [←point_image_heightSet]
    exact (hFinite H).image _
  · have he : BoundedHeightCounting.restrictedCount parameterHeight
        SecondFunctionFieldPointPlace.branchPointsᶜ=pointCount := funext restrictedCount_eq
    rw [he]
    exact hCount

end
end Z2Z4Rank6.SecondParameterCounting
