import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing
import Z2Z4Rank6.PointMap
import Mathlib.Tactic

/-!
# Scaling and quadratic untwisting on point groups

The coordinate change used before Lemma 3.1 and in Proposition 4.2 of
Manvir Jaswal, "Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and
rank at least six", DOI: 10.5281/zenodo.23437117.

The group-law formulas are Mathlib's nonsingular Weierstrass point formulas,
following Silverman, *The Arithmetic of Elliptic Curves*, Chapter III, §2.
All branches, including the identity, vertical lines and tangent lines, are
checked here.
-/

namespace Z2Z4Rank6.PointScaling

open WeierstrassCurve Affine Affine.Point
open Common.WeierstrassCoordinates

variable {K : Type*} [Field K]

/-- The short split-coefficient equation y²=x³+A x²+B x. -/
def curve (A B : K) : WeierstrassCurve K where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := B
  a₆ := 0

theorem equation_iff (A B x y : K) :
    (curve A B).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 + A * x ^ 2 + B * x := by
  rw [Affine.equation_iff]
  simp only [curve, zero_mul, add_zero]

theorem nonsingular_iff (A B x y : K) :
    (curve A B).toAffine.Nonsingular x y ↔
      y ^ 2 = x ^ 3 + A * x ^ 2 + B * x ∧
        (3 * x ^ 2 + 2 * A * x + B ≠ 0 ∨ 2 * y ≠ 0) := by
  rw [Affine.Nonsingular, equation_iff]
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY,
    curve, zero_mul, zero_sub, neg_ne_zero, add_zero]

theorem scale_equation (A B u x y : K)
    (h : (curve A B).toAffine.Equation x y) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Equation (u ^ 2 * x) (u ^ 3 * y) := by
  rw [equation_iff] at h ⊢
  linear_combination u ^ 6 * h

theorem scale_nonsingular (A B u : K) (hu : u ≠ 0) (x y : K)
    (h : (curve A B).toAffine.Nonsingular x y) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  rw [nonsingular_iff] at h ⊢
  refine ⟨(equation_iff _ _ _ _).mp (scale_equation A B u x y ((equation_iff _ _ _ _).mpr h.1)), ?_⟩
  rcases h.2 with hx | hy
  · left
    have heq : 3 * (u ^ 2 * x) ^ 2 + 2 * (u ^ 2 * A) * (u ^ 2 * x) + u ^ 4 * B =
        u ^ 4 * (3 * x ^ 2 + 2 * A * x + B) := by ring
    rw [heq]
    exact mul_ne_zero (pow_ne_zero _ hu) hx
  · right
    rw [show 2 * (u ^ 3 * y) = u ^ 3 * (2 * y) by ring]
    exact mul_ne_zero (pow_ne_zero _ hu) hy

theorem unscale_nonsingular (A B u : K) (hu : u ≠ 0) (x y : K)
    (h : (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Nonsingular x y) :
    (curve A B).toAffine.Nonsingular (u⁻¹ ^ 2 * x) (u⁻¹ ^ 3 * y) := by
  have hh := scale_nonsingular (u ^ 2 * A) (u ^ 4 * B) u⁻¹ (inv_ne_zero hu) x y h
  have hc : curve (u⁻¹ ^ 2 * (u ^ 2 * A)) (u⁻¹ ^ 4 * (u ^ 4 * B)) = curve A B := by
    ext <;> simp only [curve] <;> field_simp
  rw [hc] at hh
  exact hh

def scalePoint (A B u : K) (hu : u ≠ 0) :
    (curve A B).toAffine.Point → (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Point
  | .zero => 0
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (scale_nonsingular A B u hu x y h)

def unscalePoint (A B u : K) (hu : u ≠ 0) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Point → (curve A B).toAffine.Point
  | .zero => 0
  | .some x y h => .some (u⁻¹ ^ 2 * x) (u⁻¹ ^ 3 * y) (unscale_nonsingular A B u hu x y h)

theorem scale_left_inverse (A B u : K) (hu : u ≠ 0) :
    Function.LeftInverse (unscalePoint A B u hu) (scalePoint A B u hu) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [scalePoint, unscalePoint, Point.some.injEq]
      constructor <;> field_simp

theorem scale_right_inverse (A B u : K) (hu : u ≠ 0) :
    Function.RightInverse (unscalePoint A B u hu) (scalePoint A B u hu) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [scalePoint, unscalePoint, Point.some.injEq]
      constructor <;> field_simp

variable [DecidableEq K]

theorem scale_slope (A B u : K) (hu : u ≠ 0) (x₁ x₂ y₁ y₂ : K) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.slope
      (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
        u * (curve A B).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hx : u ^ 2 * x₁ = u ^ 2 * x₂ ↔ x₁ = x₂ :=
    ⟨mul_left_cancel₀ (pow_ne_zero _ hu), fun h => congrArg (fun x => u ^ 2 * x) h⟩
  have hy : u ^ 3 * y₁ = -(u ^ 3 * y₂) ↔ y₁ = -y₂ := by
    rw [← mul_neg]
    exact ⟨mul_left_cancel₀ (pow_ne_zero _ hu), fun h => congrArg (fun y => u ^ 3 * y) h⟩
  simp only [Affine.slope, Affine.negY, curve, zero_mul, sub_zero, hx, hy]
  split_ifs
  all_goals field_simp
  all_goals ring

omit [DecidableEq K] in
theorem scale_addX (A B u x₁ x₂ ℓ : K) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.addX (u ^ 2 * x₁) (u ^ 2 * x₂) (u * ℓ) =
      u ^ 2 * (curve A B).toAffine.addX x₁ x₂ ℓ := by
  simp only [Affine.addX, curve]
  ring

omit [DecidableEq K] in
theorem scale_addY (A B u x₁ x₂ y₁ ℓ : K) :
    (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.addY
      (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u * ℓ) =
        u ^ 3 * (curve A B).toAffine.addY x₁ x₂ y₁ ℓ := by
  simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, curve]
  ring

theorem scalePoint_add (A B u : K) (hu : u ≠ 0)
    (P Q : (curve A B).toAffine.Point) :
    scalePoint A B u hu (P + Q) = scalePoint A B u hu P + scalePoint A B u hu Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero =>
          change scalePoint A B u hu (Point.some x₁ y₁ h₁ + 0) = scalePoint A B u hu (.some x₁ y₁ h₁) + 0
          rw [add_zero, add_zero]
      | some x₂ y₂ h₂ =>
          by_cases hv : x₁ = x₂ ∧ y₁ = -y₂
          · rw [Point.add_of_Y_eq hv.1 (by simpa only [Affine.negY, curve, zero_mul, sub_zero] using hv.2)]
            simp only [scalePoint]
            exact (Point.add_of_Y_eq (by rw [hv.1]) (by
              simp only [Affine.negY, curve, zero_mul, sub_zero]
              rw [hv.2, _root_.mul_neg])).symm
          · rw [Point.add_some (by simpa only [Affine.negY, curve, zero_mul, sub_zero] using hv)]
            simp only [scalePoint]
            have hv' : ¬(u ^ 2 * x₁ = u ^ 2 * x₂ ∧
                u ^ 3 * y₁ = (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.negY
                  (u ^ 2 * x₂) (u ^ 3 * y₂)) := by
              intro h
              apply hv
              constructor
              · exact mul_left_cancel₀ (pow_ne_zero _ hu) h.1
              · apply mul_left_cancel₀ (pow_ne_zero 3 hu)
                simpa only [Affine.negY, curve, zero_mul, sub_zero, mul_neg] using h.2
            rw [Point.add_some hv']
            congr 1
            · rw [scale_slope A B u hu, scale_addX]
            · rw [scale_slope A B u hu, scale_addY]

/-- The additive equivalence induced by (x,y)↦(u²x,u³y). It is valid
even for the nonsingular point groups of a singular Weierstrass equation. -/
def scaleEquiv (A B u : K) (hu : u ≠ 0) :
    (curve A B).toAffine.Point ≃+ (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Point where
  toFun := scalePoint A B u hu
  invFun := unscalePoint A B u hu
  left_inv := scale_left_inverse A B u hu
  right_inv := scale_right_inverse A B u hu
  map_add' := scalePoint_add A B u hu

def scaleUnitEquiv (A B : K) (u : Kˣ) :
    (curve A B).toAffine.Point ≃+ (curve ((u : K) ^ 2 * A) ((u : K) ^ 4 * B)).toAffine.Point :=
  scaleEquiv A B u (Units.ne_zero u)

@[simp] theorem scaleEquiv_zero (A B u : K) (hu : u ≠ 0) : scaleEquiv A B u hu 0 = 0 := rfl

@[simp] theorem scaleEquiv_some (A B u : K) (hu : u ≠ 0) (x y : K)
    (h : (curve A B).toAffine.Nonsingular x y) :
    scaleEquiv A B u hu (.some x y h) =
      .some (u ^ 2 * x) (u ^ 3 * y) (scale_nonsingular A B u hu x y h) := rfl

@[simp] theorem scaleEquiv_symm_some (A B u : K) (hu : u ≠ 0) (x y : K)
    (h : (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Nonsingular x y) :
    (scaleEquiv A B u hu).symm (.some x y h) =
      .some (u⁻¹ ^ 2 * x) (u⁻¹ ^ 3 * y) (unscale_nonsingular A B u hu x y h) := rfl

/-- Transport between equal equations preserves point coordinates. -/
def pointCongr {W W' : WeierstrassCurve K} (h : W = W') : W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst W'
  exact AddEquiv.refl _

theorem pointCongr_some {W W' : WeierstrassCurve K} (h : W = W')
    (x y : K) (hxy : W.toAffine.Nonsingular x y) :
    ∃ hxy' : W'.toAffine.Nonsingular x y,
      pointCongr h (.some x y hxy) = .some x y hxy' := by
  subst W'
  exact ⟨hxy, rfl⟩

theorem encode_pointCongr {W W' : WeierstrassCurve K} (h : W = W')
    (P : W.toAffine.Point) : encode (pointCongr h P) = encode P := by
  subst W'
  rfl

theorem encode_scaleEquiv (A B u : K) (hu : u ≠ 0) (P : (curve A B).toAffine.Point) :
    encode (scaleEquiv A B u hu P) =
      (encode P).map (fun xy => (u ^ 2 * xy.1, u ^ 3 * xy.2)) := by
  cases P <;> rfl

theorem encode_scaleEquiv_symm (A B u : K) (hu : u ≠ 0)
    (P : (curve (u ^ 2 * A) (u ^ 4 * B)).toAffine.Point) :
    encode ((scaleEquiv A B u hu).symm P) =
      (encode P).map (fun xy => (u⁻¹ ^ 2 * xy.1, u⁻¹ ^ 3 * xy.2)) := by
  cases P <;> rfl

omit [DecidableEq K] in
private theorem root_ne_zero (d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d) : r ≠ 0 := by
  intro hz
  exact hd (by rw [← hr, hz, zero_pow (by decide)])

omit [DecidableEq K] in
theorem twist_eq_scaled (A B d r : K) (hr : r ^ 2 = d) :
    curve (d * A) (d ^ 2 * B) = curve (r ^ 2 * A) (r ^ 4 * B) := by
  have hr4 : r ^ 4 = d ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hr]
  rw [hr, hr4]

/-- The quadratic untwisting equivalence, from the d-twist to the
original curve over a field containing a chosen square root r of d. -/
def untwistEquiv (A B d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d) :
    (curve (d * A) (d ^ 2 * B)).toAffine.Point ≃+ (curve A B).toAffine.Point :=
  (pointCongr (twist_eq_scaled A B d r hr)).trans
    (scaleEquiv A B r (root_ne_zero d r hd hr)).symm

/-- The untwisting formula is exactly (x/d,y/(d r)), including the identity. -/
theorem encode_untwistEquiv (A B d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d)
    (P : (curve (d * A) (d ^ 2 * B)).toAffine.Point) :
    encode (untwistEquiv A B d r hd hr P) =
      (encode P).map (fun xy => (xy.1 / d, xy.2 / (d * r))) := by
  simp only [untwistEquiv, AddEquiv.trans_apply, encode_scaleEquiv_symm, encode_pointCongr]
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [encode, Option.map_some, Option.some.injEq, Prod.mk.injEq]
      have hr0 := root_ne_zero d r hd hr
      constructor <;> rw [← hr] <;> field_simp

def untwistHom (A B d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d) :
    (curve (d * A) (d ^ 2 * B)).toAffine.Point →+ (curve A B).toAffine.Point :=
  (untwistEquiv A B d r hd hr).toAddMonoidHom

theorem untwistHom_injective (A B d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d) :
    Function.Injective (untwistHom A B d r hd hr) := (untwistEquiv A B d r hd hr).injective

omit [DecidableEq K] in
theorem encode_neg (A B : K) (P : (curve A B).toAffine.Point) :
    encode (-P) = (encode P).map (fun xy => (xy.1, -xy.2)) := by
  cases P with
  | zero => rfl
  | some x y h =>
      rw [Point.neg_some]
      simp only [encode, Option.map_some, Affine.negY, curve, zero_mul, sub_zero]

/-- Changing the chosen square root from r to -r negates the untwisted
point. This is the character sign used in the biquadratic decomposition. -/
theorem untwistEquiv_neg_root (A B d r : K) (hd : d ≠ 0) (hr : r ^ 2 = d)
    (P : (curve (d * A) (d ^ 2 * B)).toAffine.Point) :
    untwistEquiv A B d (-r) hd (by simpa only [neg_sq] using hr) P =
      -(untwistEquiv A B d r hd hr P) := by
  apply encode_injective (curve A B).toAffine
  rw [encode_untwistEquiv, encode_neg, encode_untwistEquiv, Option.map_map]
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [encode, Option.map_some, Function.comp_apply, Option.some.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · rw [_root_.mul_neg, div_neg]

variable {L : Type*} [Field L] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
theorem map_curve (f : K →+* L) (A B : K) :
    (curve A B).map f = curve (f A) (f B) := by
  ext <;> simp [curve, WeierstrassCurve.map]

omit [DecidableEq K] [DecidableEq L] in
private theorem image_ne_zero (f : K →+* L) (d : K) (hd : d ≠ 0) : f d ≠ 0 := by
  intro hz
  apply hd
  apply f.injective
  simpa only [_root_.map_zero] using hz

omit [DecidableEq K] [DecidableEq L] in
private theorem mapped_twist_eq (f : K →+* L) (A B d : K) :
    (curve (d * A) (d ^ 2 * B)).map f = curve (f d * f A) ((f d) ^ 2 * f B) := by
  rw [map_curve, map_mul, map_mul, map_pow]

/-- Base change of a rational twist point followed by the untwisting
equivalence. This is the homomorphism whose image gives a new character space. -/
noncomputable def baseChangeUntwistHom (f : K →+* L) (A B d : K) (r : L)
    (hd : d ≠ 0) (hr : r ^ 2 = f d) :
    (curve (d * A) (d ^ 2 * B)).toAffine.Point →+ (curve (f A) (f B)).toAffine.Point :=
  (untwistHom (f A) (f B) (f d) r (image_ne_zero f d hd) hr).comp
    ((pointCongr (mapped_twist_eq f A B d)).toAddMonoidHom.comp
      (fieldPointMap f (curve (d * A) (d ^ 2 * B))))

theorem encode_baseChangeUntwistHom (f : K →+* L) (A B d : K) (r : L)
    (hd : d ≠ 0) (hr : r ^ 2 = f d) (P : (curve (d * A) (d ^ 2 * B)).toAffine.Point) :
    encode (baseChangeUntwistHom f A B d r hd hr P) =
      (encode P).map (fun xy => (f xy.1 / f d, f xy.2 / (f d * r))) := by
  change encode (untwistEquiv (f A) (f B) (f d) r (image_ne_zero f d hd) hr
    (pointCongr (mapped_twist_eq f A B d) (fieldPointMap f _ P))) = _
  rw [encode_untwistEquiv, encode_pointCongr, encode_fieldPointMap, Option.map_map]
  rfl

private theorem fieldPointMap_injective (f : K →+* L) (W : WeierstrassCurve K) :
    Function.Injective (fieldPointMap f W) := by
  intro P Q hPQ
  apply encode_injective W.toAffine
  have hh := congrArg encode hPQ
  rw [encode_fieldPointMap, encode_fieldPointMap] at hh
  cases P <;> cases Q <;> simp_all [encode, f.injective.eq_iff]

theorem baseChangeUntwistHom_injective (f : K →+* L) (A B d : K) (r : L)
    (hd : d ≠ 0) (hr : r ^ 2 = f d) :
    Function.Injective (baseChangeUntwistHom f A B d r hd hr) :=
  (untwistHom_injective (f A) (f B) (f d) r (image_ne_zero f d hd) hr).comp
    ((pointCongr (mapped_twist_eq f A B d)).injective.comp (fieldPointMap_injective f _))

end Z2Z4Rank6.PointScaling

namespace Z2Z4Rank6.PointScaling

open scoped TensorProduct

variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup J]

/-- Rationalization of an additive homomorphism of point groups. -/
def rationalizeHom (f : G →+ H) : ℚ ⊗[ℤ] G →ₗ[ℚ] ℚ ⊗[ℤ] H :=
  f.toIntLinearMap.baseChange ℚ

@[simp] theorem rationalizeHom_tmul (f : G →+ H) (q : ℚ) (P : G) :
    rationalizeHom f (q ⊗ₜ[ℤ] P) = q ⊗ₜ[ℤ] f P := rfl

theorem rationalizeHom_injective (f : G →+ H) (hf : Function.Injective f) :
    Function.Injective (rationalizeHom f) := by
  let _ : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) f.toIntLinearMap hf

/-- Rationalization preserves additive equivalences. -/
def rationalizeEquiv (e : G ≃+ H) : ℚ ⊗[ℤ] G ≃ₗ[ℚ] ℚ ⊗[ℤ] H :=
  e.toIntLinearEquiv.baseChange ℤ ℚ G H

@[simp] theorem rationalizeEquiv_tmul (e : G ≃+ H) (q : ℚ) (P : G) :
    rationalizeEquiv e (q ⊗ₜ[ℤ] P) = q ⊗ₜ[ℤ] e P := rfl

theorem rationalizeHom_comp (f : G →+ H) (g : H →+ J) :
    rationalizeHom (g.comp f) = (rationalizeHom g).comp (rationalizeHom f) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q P => rfl
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

theorem rationalizeHom_involutive (f : G →+ G) (hf : ∀ P, f (f P) = P) :
    (rationalizeHom f).comp (rationalizeHom f) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q P => simp only [LinearMap.comp_apply, rationalizeHom_tmul, hf, LinearMap.id_apply]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add, LinearMap.id_apply] at hx hy ⊢; rw [hx, hy]

theorem rationalizeHom_commute (f g : G →+ G) (hfg : ∀ P, f (g P) = g (f P)) :
    (rationalizeHom f).comp (rationalizeHom g) = (rationalizeHom g).comp (rationalizeHom f) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q P => simp only [LinearMap.comp_apply, rationalizeHom_tmul, hfg]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]

end Z2Z4Rank6.PointScaling
