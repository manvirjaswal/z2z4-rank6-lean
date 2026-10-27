import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Local polynomial invariants of a Weierstrass family

The definitions here are orders of the Weierstrass invariants.
They do not define a Kodaira fiber type or a resolved surface. The multiplicative criterion is the input to Miranda, The Basic Theory of
Elliptic Surfaces (1989), Table IV.3.1, p. 41. The geometric fiber
interpretation is stated in ComplexEllipticSurfaceTheorems.
-/

namespace Common.Elliptic.SurfaceLocalData

noncomputable section
open Polynomial

variable {K : Type*} [Field K]

/-- Removing a nonvanishing cofactor determines the vanishing order. -/
theorem rootMultiplicity_of_factorization (p q : K[X]) (t : K) (n : ℕ)
    (h : p = q * (X-C t)^n) (hq : q.eval t ≠ 0) : p.rootMultiplicity t = n := by
  have hq0 : q ≠ 0 := by intro hz; exact hq (by simp [hz])
  rw [h,rootMultiplicity_mul_X_sub_C_pow hq0,rootMultiplicity_eq_zero hq,zero_add]

/-- Multiplicities of powers, including exponent zero. -/
theorem rootMultiplicity_pow (p : K[X]) (hp : p ≠ 0) (t : K) (n : ℕ) :
    (p^n).rootMultiplicity t = n * p.rootMultiplicity t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp),ih]
    simp [Nat.succ_mul]

/-- The vanishing order of the polynomial discriminant at a
finite parameter. The zero polynomial has order zero in this API, so
the separate nonzero-discriminant condition must always be retained. -/
def discriminantOrder (W : WeierstrassCurve K[X]) (t : K) : ℕ :=
  W.Δ.rootMultiplicity t

/-- An integral polynomial chart is semistable at `t` when its
discriminant is nonzero and either its discriminant or c4 is a unit
in the local ring at `t`, equivalently has nonzero evaluation. -/
def SemistableAt (W : WeierstrassCurve K[X]) (t : K) : Prop :=
  W.Δ ≠ 0 ∧ (W.Δ.eval t ≠ 0 ∨ W.c₄.eval t ≠ 0)

/-- The local Weierstrass data for a multiplicative fiber of
discriminant order `n`. This deliberately asserts no Kodaira type. -/
def MultiplicativeData (W : WeierstrassCurve K[X]) (t : K) (n : ℕ) : Prop :=
  W.Δ ≠ 0 ∧ W.c₄.eval t ≠ 0 ∧ 0 < n ∧ discriminantOrder W t = n

/-- The local Weierstrass data for good reduction. -/
def GoodData (W : WeierstrassCurve K[X]) (t : K) : Prop :=
  W.Δ.eval t ≠ 0

theorem GoodData.discriminant_ne_zero {W : WeierstrassCurve K[X]} {t : K}
    (h : GoodData W t) : W.Δ ≠ 0 := by
  intro hz
  exact h (by simp [hz])

theorem GoodData.order_eq_zero {W : WeierstrassCurve K[X]} {t : K}
    (h : GoodData W t) : discriminantOrder W t = 0 :=
  rootMultiplicity_eq_zero h

theorem MultiplicativeData.semistable {W : WeierstrassCurve K[X]} {t : K} {n : ℕ}
    (h : MultiplicativeData W t n) : SemistableAt W t :=
  ⟨h.1, Or.inr h.2.1⟩

theorem MultiplicativeData.discriminant_eq_zero {W : WeierstrassCurve K[X]}
    {t : K} {n : ℕ} (h : MultiplicativeData W t n) : W.Δ.eval t = 0 := by
  apply (rootMultiplicity_pos h.1).mp
  change 0 < discriminantOrder W t
  rw [h.2.2.2]
  exact h.2.2.1

end
end Common.Elliptic.SurfaceLocalData
