import Z2Z4Rank6.QuadraticFieldLift
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Explicit quadratic rational-function presentations

A transcendental x and a root y of the mapped quadratic relation construct a
field homomorphism from the quadratic root field over Q(X). If x,y
generate the target field, the homomorphism is a Q-algebra equivalence.
-/
namespace Z2Z4Rank6.QuadraticRatFuncEquiv
noncomputable section
open Polynomial
variable {L : Type*} [Field L] [Algebra ℚ L]

def baseEmbedding (x : L) (hx : Transcendental ℚ x) : RatFunc ℚ→+*L :=
  RatFunc.liftRingHom (aeval x).toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.mp hx))

@[simp] theorem baseEmbedding_X (x : L) (hx : Transcendental ℚ x) : baseEmbedding x hx RatFunc.X=x := by
  unfold baseEmbedding
  rw [RatFunc.liftRingHom_X]
  simp

variable (d : RatFunc ℚ) [Fact (¬IsSquare d)]

abbrev Source := QuadraticAlgebra (RatFunc ℚ) d 0

def embedding (x y : L) (hx : Transcendental ℚ x) (hy : y^2=baseEmbedding x hx d) :
    Source d→ₐ[ℚ]L :=
  ringHomToRatAlgHom (quadraticFieldLift d (baseEmbedding x hx) y hy)

@[simp] theorem embedding_X (x y : L) (hx : Transcendental ℚ x) (hy : y^2=baseEmbedding x hx d) :
    embedding d x y hx hy (algebraMap (RatFunc ℚ) (Source d) RatFunc.X)=x := by
  simp only [embedding,ringHomToRatAlgHom_apply,quadraticFieldLift_algebraMap,baseEmbedding_X]

@[simp] theorem embedding_y (x y : L) (hx : Transcendental ℚ x) (hy : y^2=baseEmbedding x hx d) :
    embedding d x y hx hy QuadraticAlgebra.omega=y := by
  simp only [embedding,ringHomToRatAlgHom_apply,quadraticFieldLift_omega]

theorem embedding_surjective (x y : L) (hx : Transcendental ℚ x) (hy : y^2=baseEmbedding x hx d)
    (hgen : IntermediateField.adjoin ℚ ({x,y}:Set L)=⊤) :
    Function.Surjective (embedding d x y hx hy) := by
  have hxx : x∈(embedding d x y hx hy).fieldRange :=
    ⟨algebraMap (RatFunc ℚ) (Source d) RatFunc.X,embedding_X d x y hx hy⟩
  have hyy : y∈(embedding d x y hx hy).fieldRange :=
    ⟨QuadraticAlgebra.omega,embedding_y d x y hx hy⟩
  have hle : IntermediateField.adjoin ℚ ({x,y}:Set L)≤(embedding d x y hx hy).fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxx
    · exact hyy
  rw [hgen] at hle
  intro z
  exact hle (by trivial)

def equiv (x y : L) (hx : Transcendental ℚ x) (hy : y^2=baseEmbedding x hx d)
    (hgen : IntermediateField.adjoin ℚ ({x,y}:Set L)=⊤) : Source d ≃ₐ[ℚ]L :=
  AlgEquiv.ofBijective (embedding d x y hx hy)
    ⟨(embedding d x y hx hy).injective,embedding_surjective d x y hx hy hgen⟩

end
end Z2Z4Rank6.QuadraticRatFuncEquiv
