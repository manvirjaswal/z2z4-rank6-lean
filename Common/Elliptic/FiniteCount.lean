import Common.Elliptic.ShortWeierstrass
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! # Linear-size enumeration of a finite short-Weierstrass group

Euler's criterion determines the number of square roots of each right-hand side.
The resulting sum has one term per field element, rather than one per coordinate
pair. The equivalence to the Mathlib point group is proved.
-/

namespace Common.ShortWeierstrass

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev SquareRoots (a : F) := {y : F // y ^ 2 = a}

instance (a : F) : Fintype (SquareRoots a) :=
  inferInstanceAs (Fintype {y : F // y ^ 2 = a})

def affineFiberEquiv (c : F) : AffineSolutions c ≃ Σ x : F, SquareRoots (x ^ 3 + c) where
  toFun P := ⟨P.val.1, ⟨P.val.2, P.property⟩⟩
  invFun P := ⟨(P.1, P.2.val), P.2.property⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

theorem affine_card_sum (c : F) :
    Fintype.card (AffineSolutions c) = ∑ x : F, Fintype.card (SquareRoots (x ^ 3 + c)) := by
  rw [Fintype.card_congr (affineFiberEquiv c), Fintype.card_sigma]

/-- A computable square-root count using only field exponentiation. -/
def squareRootCount (a : F) : ℕ :=
  if a = 0 then 1 else if npowBinRec (Fintype.card F / 2) a = 1 then 2 else 0

omit [Fintype F] [DecidableEq F] in
theorem binPower_eq_power (n : ℕ) (a : F) : npowBinRec n a = a ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

theorem card_squareRoots (hF : ringChar F ≠ 2) (a : F) :
    Fintype.card (SquareRoots a) = squareRootCount a := by
  have hc : (Fintype.card (SquareRoots a) : ℤ) = quadraticChar F a + 1 := by
    change (Fintype.card {y : F // y ^ 2 = a} : ℤ) = _
    rw [Fintype.card_of_subtype (p := fun y : F => y ^ 2 = a)
      ({y : F | y ^ 2 = a}.toFinset) (fun y => by simp)]
    exact quadraticChar_card_sqrts hF a
  apply Int.natCast_inj.mp
  rw [hc]
  by_cases ha : a = 0
  · subst a
    simp [squareRootCount]
  · rw [quadraticChar_apply, quadraticCharFun_eq_pow_of_char_ne_two hF ha]
    simp only [squareRootCount, binPower_eq_power, ha]
    split <;> norm_num

theorem card_point_linear (c : F) [(model c).IsElliptic] (hF : ringChar F ≠ 2) :
    Nat.card (Point c) = (∑ x : F, squareRootCount (x ^ 3 + c)) + 1 := by
  rw [card_point, affine_card_sum]
  simp only [card_squareRoots hF]

end Common.ShortWeierstrass
