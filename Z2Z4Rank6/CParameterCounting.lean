module

public import Z2Z4Rank6.NeronRigidCounting
public import Z2Z4Rank6.CPointPlaceEquiv
public import Z2Z4Rank6.ECMathlibFunctionFieldIso
public import Z2Z4Rank6.ECExactRank

@[expose] public section

/-!
# Counting rational C-points by the printed parameter height

The parameter-counting step of Jaswal, Remark 6.3,
DOI 10.5281/zenodo.23437117. The hypotheses are Néron's counting theorem and those of the EC rank
proof.
This file does not assert the minimal elliptic-curve height comparison.
-/

namespace Z2Z4Rank6.CParameterCounting
open scoped Classical
noncomputable section

local instance cCountingScalarTower :
    @IsScalarTower ℚ (RatFunc ℚ) FunctionField.K
      (inferInstance : SMul ℚ (RatFunc ℚ))
      (Algebra.toSMul : SMul (RatFunc ℚ) FunctionField.K)
      (Algebra.toSMul : SMul ℚ FunctionField.K) := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=RatFunc ℚ) (A:=FunctionField.K)
    (Subsingleton.elim _ _)

local instance cCountingFiniteDimensional : FiniteDimensional (RatFunc ℚ) FunctionField.K :=
  Module.Finite.of_basis FunctionField.basis

def heightSet (H : ℕ) : Set CPoint := {c | rationalParameterHeight c.m≤H}

def count (H : ℕ) : ℕ := (heightSet H).ncard

theorem place_image_heightSet (H : ℕ) :
    CPointPlaceEquiv.equiv '' heightSet H=rigidPlaceHeightSet FunctionField.K H := by
  ext v
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact hc
  · intro hv
    refine ⟨CPointPlaceEquiv.equiv.symm v,?_,CPointPlaceEquiv.equiv.apply_symm_apply v⟩
    exact hv

theorem count_eq_rigidPlaceCount (H : ℕ) :
    count H=rigidPlaceCount FunctionField.K H := by
  rw [count,rigidPlaceCount,←place_image_heightSet]
  exact (Set.ncard_image_of_injective _ CPointPlaceEquiv.equiv.injective).symm

/-- All C-points with bounded reduced m-height form a finite set. -/
theorem heightSet_finite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (H : ℕ) : (heightSet H).Finite := by
  obtain ⟨hfinite,_⟩ := rigid_place_counting hN FunctionField.K EC
    ECMathlibFunctionFieldIso.cFunctionFieldEquivMathlib 1 (by decide)
    (ec_rank_eq_one hMW hDescent hOdd)
  exact ((place_image_heightSet H).symm ▸ hfinite H).of_finite_image
    CPointPlaceEquiv.equiv.injective.injOn

/-- The bounded-parameter C-point count is (log H)^(1/2+o(1)). -/
theorem counting_exponent (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) : HasLogarithmicCountingExponent count (1/2) := by
  obtain ⟨_,hexp⟩ := rigid_place_counting hN FunctionField.K EC
    ECMathlibFunctionFieldIso.cFunctionFieldEquivMathlib 1 (by decide)
    (ec_rank_eq_one hMW hDescent hOdd)
  have he : rigidPlaceCount FunctionField.K=count :=
    funext (fun H => (count_eq_rigidPlaceCount H).symm)
  rw [he] at hexp
  simpa only [Nat.cast_one] using hexp

end
end Z2Z4Rank6.CParameterCounting
