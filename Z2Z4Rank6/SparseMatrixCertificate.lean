import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-! # A proved sparse evaluator for exact matrix certificates

The finite support of each left row is computed before the output-column
function is formed. Zero coefficients therefore do not trigger evaluation
of irrelevant entries in a large right-hand matrix.
-/
namespace Z2Z4Rank6.SparseMatrixCertificate

variable {R : Type*} [Semiring R] [DecidableEq R]
variable {m n k : Type*} [Fintype k]

/-- Matrix multiplication with the left row support computed first. -/
def sparseMul (A : Matrix m k R) (B : Matrix k n R) : Matrix m n R := fun i =>
  let support := Finset.univ.filter (fun t => A i t ≠ 0)
  fun j => ∑ t∈support, A i t*B t j

/-- The sparse evaluator is exactly ordinary matrix multiplication. -/
theorem sparseMul_eq_mul (A : Matrix m k R) (B : Matrix k n R) :
    sparseMul A B=A*B := by
  ext i j
  simp only [sparseMul,Matrix.mul_apply,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : A i t=0 <;> simp [h]

end Z2Z4Rank6.SparseMatrixCertificate
