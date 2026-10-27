import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Arithmetic input rows for Mulholland's two-adic classification

J. T. Mulholland, *Elliptic curves with rational 2-torsion and related
ternary Diophantine equations*, UBC PhD thesis (2006), Theorem 2.1,
p. 13, Table 2.1, p. 15; proofs of cases (iii)--(v), pp. 18--20.
The rows used here have odd a, v₂(b)=2,3,4. They give types I₁*, I₂*,
I₄* under the specified congruences. Only their arithmetic hypotheses
are defined here.
-/

namespace Common.Elliptic.MulhollandTwoAdic
open WeierstrassCurve

/-- The Weierstrass equation y²=x³+ax²+bx. -/
def equation (a b : ℤ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := a
  a₃ := 0
  a₄ := b
  a₆ := 0

/-- The integral translation x=X+r, without a scaling. -/
def translation (r : ℤ) : VariableChange ℤ := ⟨1, r, 0, 0⟩

/-- Three rows of the published table, parameterized by their I-star index.
This is arithmetic data, not a definition of the Kodaira type. -/
def IStarRow (a b : ℤ) (m : ℕ) : Prop :=
  padicValNat 2 a.natAbs = 0 ∧
    ((padicValNat 2 b.natAbs = 2 ∧ a % 4 = 1 ∧ m = 1) ∨
      (padicValNat 2 b.natAbs = 3 ∧ a % 4 = 3 ∧ m = 2) ∨
      (padicValNat 2 b.natAbs = 4 ∧ a % 4 = 3 ∧ m = 4))

theorem discriminant (a b : ℤ) :
    (equation a b).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp only [equation, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem translation_discriminant (W : WeierstrassCurve ℤ) (r : ℤ) :
    (translation r • W).Δ = W.Δ := by
  rw [WeierstrassCurve.variableChange_Δ]
  simp [translation]

end Common.Elliptic.MulhollandTwoAdic
