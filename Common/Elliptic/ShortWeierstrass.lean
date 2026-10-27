module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Fintype.Option
public import Mathlib.Tactic

@[expose] public section

/-! # Computable coordinates for short-Weierstrass point groups

The coordinate arithmetic below is proved to encode Mathlib's group law.
It can therefore certify point counts and multiples.
-/

namespace Common.ShortWeierstrass

open WeierstrassCurve.Affine

variable {F : Type*} [Field F]

def model (c : F) : WeierstrassCurve F := ⟨0, 0, 0, 0, c⟩

abbrev Point (c : F) := (model c).toAffine.Point

theorem discriminant (c : F) : (model c).Δ = -432 * c ^ 2 := by
  norm_num [model, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem equation_iff (c x y : F) :
    (model c).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + c := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [model]

def encode {c : F} : Point c → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

theorem encode_injective (c : F) : Function.Injective (encode (c := c)) := by
  intro P Q h
  cases P <;> cases Q <;> simp_all [encode]

def coordinateAdd [DecidableEq F] : Option (F × F) → Option (F × F) → Option (F × F)
  | none, Q => Q
  | P, none => P
  | some (x₁, y₁), some (x₂, y₂) =>
      if x₁ = x₂ ∧ y₁ = -y₂ then none else
        let l := if x₁ = x₂ then 3 * x₁ ^ 2 / (2 * y₁) else (y₁ - y₂) / (x₁ - x₂)
        let x₃ := l ^ 2 - x₁ - x₂
        some (x₃, -y₁ - l * (x₃ - x₁))

theorem encode_add [DecidableEq F] {c : F} (P Q : Point c) :
    encode (P + Q) = coordinateAdd (encode P) (encode Q) := by
  cases P with
  | zero =>
    change encode ((0 : Point c) + Q) = _
    rw [zero_add]
    rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change encode (Point.some x₁ y₁ h₁ + (0 : Point c)) = _
      rw [add_zero]
      rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = -y₂
      · rw [Point.add_of_Y_eq hxy.1 (by simpa [model, negY] using hxy.2)]
        simp [encode, coordinateAdd, hxy]
      · rw [Point.add_some (by simpa [model, negY] using hxy)]
        simp only [encode, coordinateAdd, ite_eq_right hxy]
        congr 1
        by_cases hx : x₁ = x₂
        · have hy : y₁ ≠ (model c).toAffine.negY x₂ y₂ := by
            simpa [model, negY] using fun h => hxy ⟨hx, h⟩
          rw [slope_of_Y_ne hx hy]
          simp [model, negY, addX, addY, negAddY, hx]
          ring_nf
          simp
        · rw [slope_of_X_ne hx]
          simp [model, negY, addX, addY, negAddY, hx]
          ring

def coordinateMul [DecidableEq F] : ℕ → Option (F × F) → Option (F × F)
  | 0, _ => none
  | n + 1, P => coordinateAdd (coordinateMul n P) P

theorem encode_nsmul [DecidableEq F] {c : F} (n : ℕ) (P : Point c) :
    encode (n • P) = coordinateMul n (encode P) := by
  induction n with
  | zero => simp [encode, coordinateMul]
  | succ n ih => rw [succ_nsmul, encode_add, ih]; rfl

def AffineSolutions (c : F) := {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + c}

instance [Fintype F] [DecidableEq F] (c : F) : Fintype (AffineSolutions c) :=
  inferInstanceAs (Fintype {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 + c})

def pointCoordinateEquiv (c : F) [(model c).IsElliptic] :
    Point c ≃ Option (AffineSolutions c) :=
  ((model c).toAffine.pointEquiv).trans
    (Equiv.subtypeEquivRight (fun xy : F × F => equation_iff c xy.1 xy.2)).optionCongr

theorem card_point [Fintype F] [DecidableEq F] (c : F) [(model c).IsElliptic] :
    Nat.card (Point c) = Fintype.card (AffineSolutions c) + 1 := by
  rw [Nat.card_congr (pointCoordinateEquiv c), Nat.card_eq_fintype_card,
    Fintype.card_option]

end Common.ShortWeierstrass
