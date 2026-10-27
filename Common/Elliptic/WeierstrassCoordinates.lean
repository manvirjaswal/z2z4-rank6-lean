import Common.Elliptic.FiniteCount

/-! # Computable coordinates for arbitrary Weierstrass point groups

The coordinate addition uses Mathlib's own slope and addition formulas and is
proved to encode its point-group law. This also covers long Weierstrass models.
-/

namespace Common.WeierstrassCoordinates

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

def encode {W : WeierstrassCurve.Affine F} : W.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

theorem encode_injective (W : WeierstrassCurve.Affine F) :
    Function.Injective (encode (W := W)) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [encode]

def coordinateAdd [DecidableEq F] (W : WeierstrassCurve.Affine F) :
    Option (F × F) → Option (F × F) → Option (F × F)
  | none, Q => Q
  | P, none => P
  | some (x₁, y₁), some (x₂, y₂) =>
      if x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then none else
        let l := W.slope x₁ x₂ y₁ y₂
        some (W.addX x₁ x₂ l, W.addY x₁ x₂ y₁ l)

theorem encode_add [DecidableEq F] {W : WeierstrassCurve.Affine F} (P Q : W.Point) :
    encode (P + Q) = coordinateAdd W (encode P) (encode Q) := by
  cases P with
  | zero =>
    change encode ((0 : W.Point) + Q) = _
    rw [zero_add]
    rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change encode (Point.some x₁ y₁ h₁ + (0 : W.Point)) = _
      rw [add_zero]
      rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        simp [encode, coordinateAdd, hxy]
      · rw [Point.add_some hxy]
        simp only [encode, coordinateAdd, ite_eq_right hxy]

def coordinateMul [DecidableEq F] (W : WeierstrassCurve.Affine F) :
    ℕ → Option (F × F) → Option (F × F)
  | 0, _ => none
  | n + 1, P => coordinateAdd W (coordinateMul W n P) P

theorem encode_nsmul [DecidableEq F] {W : WeierstrassCurve.Affine F} (n : ℕ) (P : W.Point) :
    encode (n • P) = coordinateMul W n (encode P) := by
  induction n with
  | zero => simp [encode, coordinateMul]
  | succ n ih => rw [succ_nsmul, encode_add, ih]; rfl

def AffineSolutions (W : WeierstrassCurve.Affine F) := {xy : F × F //
  xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
    xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆}

instance [Fintype F] [DecidableEq F] (W : WeierstrassCurve.Affine F) :
    Fintype (AffineSolutions W) := inferInstanceAs
  (Fintype {xy : F × F // xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
    xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆})

def pointCoordinateEquiv (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    W.Point ≃ Option (AffineSolutions W) :=
  W.pointEquiv.trans (Equiv.subtypeEquivRight (fun xy : F × F =>
    (by rw [WeierstrassCurve.Affine.equation_iff] :
      W.Equation xy.1 xy.2 ↔ xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆))).optionCongr

theorem card_point [Fintype F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
    [W.IsElliptic] : Nat.card W.Point = Fintype.card (AffineSolutions W) + 1 := by
  rw [Nat.card_congr (pointCoordinateEquiv W), Nat.card_eq_fintype_card,
    Fintype.card_option]

def longModel (a₂ a₄ a₆ : F) : WeierstrassCurve.Affine F := ⟨0, a₂, 0, a₄, a₆⟩

variable [Fintype F] [DecidableEq F]

def longAffineFiberEquiv (a₂ a₄ a₆ : F) :
    AffineSolutions (longModel a₂ a₄ a₆) ≃
      Σ x : F, ShortWeierstrass.SquareRoots (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) where
  toFun P := ⟨P.val.1, ⟨P.val.2, by simpa [longModel] using P.property⟩⟩
  invFun P := ⟨(P.1, P.2.val), by simpa [longModel] using P.2.property⟩
  left_inv P := by cases P; rfl
  right_inv P := by cases P; rfl

theorem card_point_long_linear (a₂ a₄ a₆ : F) [(longModel a₂ a₄ a₆).IsElliptic]
    (hF : ringChar F ≠ 2) :
    Nat.card (longModel a₂ a₄ a₆).Point =
      (∑ x : F, ShortWeierstrass.squareRootCount (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)) + 1 := by
  rw [card_point, Fintype.card_congr (longAffineFiberEquiv a₂ a₄ a₆), Fintype.card_sigma]
  simp only [ShortWeierstrass.card_squareRoots hF]

end Common.WeierstrassCoordinates
