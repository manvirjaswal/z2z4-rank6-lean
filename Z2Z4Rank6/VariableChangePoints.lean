import Z2Z4Rank6.PointScaling
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Admissible variable changes on elliptic point groups

Mathlib defines the coefficient action of an admissible Weierstrass change.
This file constructs its additive equivalence on nonsingular affine points
of elliptic curves, including the point at infinity. The coordinate and
group-law identities follow Silverman, *The Arithmetic of Elliptic Curves*,
second edition, Chapter III, §1 and §2, and are proved directly here.
-/

namespace Z2Z4Rank6.VariableChangePoints

open WeierstrassCurve Affine Affine.Point

noncomputable section
variable {K : Type*} [Field K]

def coordX (C : VariableChange K) (x : K) : K := (C.u : K)^2*x+C.r
def coordY (C : VariableChange K) (x y : K) : K :=
  (C.u : K)^3*y+(C.u : K)^2*C.s*x+C.t

private def residual (W : WeierstrassCurve K) (x y : K) : K :=
  y^2+W.a₁*x*y+W.a₃*y-(x^3+W.a₂*x^2+W.a₄*x+W.a₆)

private theorem residual_change (W : WeierstrassCurve K) (C : VariableChange K) (x y : K) :
    residual W (coordX C x) (coordY C x y) = (C.u : K)^6*residual (C • W) x y := by
  simp only [residual,coordX,coordY,variableChange_def,Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem equation_residual (W : WeierstrassCurve K) (x y : K) :
    W.toAffine.Equation x y ↔ residual W x y = 0 := by
  rw [Affine.equation_iff]
  exact sub_eq_zero.symm

theorem equation_change (W : WeierstrassCurve K) (C : VariableChange K) (x y : K) :
    W.toAffine.Equation (coordX C x) (coordY C x y) ↔
      (C • W).toAffine.Equation x y := by
  rw [equation_residual,equation_residual,residual_change,mul_eq_zero]
  simp only [pow_ne_zero 6 C.u.ne_zero,false_or]

def invX (C : VariableChange K) (x : K) : K := (C.u : K)⁻¹^2*(x-C.r)
def invY (C : VariableChange K) (x y : K) : K :=
  (C.u : K)⁻¹^3*(y-C.s*(x-C.r)-C.t)

theorem coord_invX (C : VariableChange K) (x : K) : coordX C (invX C x) = x := by
  simp only [coordX,invX]
  field_simp
  ring

theorem coord_invY (C : VariableChange K) (x y : K) :
    coordY C (invX C x) (invY C x y) = y := by
  simp only [coordY,invX,invY]
  field_simp
  ring

theorem inv_coordX (C : VariableChange K) (x : K) : invX C (coordX C x) = x := by
  simp only [coordX,invX]
  field_simp
  ring

theorem inv_coordY (C : VariableChange K) (x y : K) :
    invY C (coordX C x) (coordY C x y) = y := by
  simp only [coordX,coordY,invY]
  field_simp
  ring

variable (W : WeierstrassCurve K) (C : VariableChange K) [W.IsElliptic]

def forward : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y h => .mk ((equation_change W C x y).mpr h.1)

def backward : W.toAffine.Point → (C • W).toAffine.Point
  | .zero => 0
  | .some x y h => .mk (x := invX C x) (y := invY C x y) (by
      apply (equation_change W C _ _).mp
      simpa only [coord_invX,coord_invY] using h.1)

theorem backward_forward : Function.LeftInverse (backward W C) (forward W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp only [forward,backward,Point.mk,inv_coordX,inv_coordY]

theorem forward_backward : Function.RightInverse (backward W C) (forward W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp only [forward,backward,Point.mk,coord_invX,coord_invY]

omit [W.IsElliptic] in
theorem coordX_injective : Function.Injective (coordX C) := by
  intro x y h
  exact mul_left_cancel₀ (pow_ne_zero 2 C.u.ne_zero) (add_right_cancel h)

omit [W.IsElliptic] in
theorem coordY_injective (x : K) : Function.Injective (coordY C x) := by
  intro y z h
  exact mul_left_cancel₀ (pow_ne_zero 3 C.u.ne_zero) (add_right_cancel (add_right_cancel h))

omit [W.IsElliptic] in
theorem negY_change (x y : K) :
    W.toAffine.negY (coordX C x) (coordY C x y) =
      coordY C x ((C • W).toAffine.negY x y) := by
  simp only [negY,coordX,coordY,variableChange_def,Units.val_inv_eq_inv_val]
  field_simp
  ring

omit [W.IsElliptic] in
theorem vertical_iff (x₁ x₂ y₁ y₂ : K) :
    (coordX C x₁ = coordX C x₂ ∧
      coordY C x₁ y₁ = W.toAffine.negY (coordX C x₂) (coordY C x₂ y₂)) ↔
    (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  constructor
  · rintro ⟨hx,hy⟩
    have he := coordX_injective C hx
    refine ⟨he,?_⟩
    rw [he,negY_change] at hy
    exact coordY_injective C x₂ hy
  · rintro ⟨rfl,hy⟩
    exact ⟨rfl,by rw [hy,negY_change]⟩

omit [W.IsElliptic] in
theorem addX_change (x₁ x₂ ℓ : K) :
    W.toAffine.addX (coordX C x₁) (coordX C x₂) ((C.u : K)*ℓ+C.s) =
      coordX C ((C • W).toAffine.addX x₁ x₂ ℓ) := by
  simp only [addX,coordX,variableChange_def,Units.val_inv_eq_inv_val]
  field_simp
  ring

omit [W.IsElliptic] in
theorem addY_change (x₁ x₂ y₁ ℓ : K) :
    W.toAffine.addY (coordX C x₁) (coordX C x₂) (coordY C x₁ y₁) ((C.u : K)*ℓ+C.s) =
      coordY C ((C • W).toAffine.addX x₁ x₂ ℓ) ((C • W).toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY,negAddY,addX,negY,coordX,coordY,variableChange_def,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

omit [W.IsElliptic] in
private theorem tangent_den_change (x y : K) :
    coordY C x y-W.toAffine.negY (coordX C x) (coordY C x y) =
      (C.u : K)^3*(y-(C • W).toAffine.negY x y) := by
  rw [negY_change]
  simp only [coordY]
  ring

omit [W.IsElliptic] in
private theorem tangent_num_change (x y : K) :
    3*(coordX C x)^2+2*W.a₂*(coordX C x)+W.a₄-W.a₁*(coordY C x y) =
      (C.u : K)^4*(3*x^2+2*(C • W).a₂*x+(C • W).a₄-(C • W).a₁*y)+
      C.s*(C.u : K)^3*(y-(C • W).toAffine.negY x y) := by
  simp only [coordX,coordY,negY,variableChange_def,Units.val_inv_eq_inv_val]
  field_simp
  ring

variable [DecidableEq K]

omit [W.IsElliptic] in
theorem slope_change (x₁ x₂ y₁ y₂ : K)
    (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hv : ¬(x₁=x₂ ∧ y₁=(C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (coordX C x₁) (coordX C x₂) (coordY C x₁ y₁) (coordY C x₂ y₂) =
      (C.u : K)*(C • W).toAffine.slope x₁ x₂ y₁ y₂+C.s := by
  have hv' := mt (vertical_iff W C x₁ x₂ y₁ y₂).mp hv
  by_cases hx : x₁=x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h => hv ⟨hx,h⟩
    have hy' : coordY C x₁ y₁ ≠ W.toAffine.negY (coordX C x₂) (coordY C x₂ y₂) :=
      fun h => hv' ⟨congrArg (coordX C) hx,h⟩
    have hyy : y₁=y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    have hd : y₁-(C • W).toAffine.negY x₁ y₁ ≠ 0 := by
      apply sub_ne_zero.mpr
      simpa only [←hx,←hyy] using hy
    rw [Affine.slope_of_Y_ne (congrArg (coordX C) hx) hy',Affine.slope_of_Y_ne hx hy,
      tangent_num_change,tangent_den_change]
    field_simp
  · have hx' : coordX C x₁ ≠ coordX C x₂ := fun h => hx (coordX_injective C h)
    rw [Affine.slope_of_X_ne hx',Affine.slope_of_X_ne hx]
    simp only [coordX,coordY]
    have hd : (C.u : K)^2*x₁-(C.u : K)^2*x₂ ≠ 0 := by
      rw [←mul_sub]
      exact mul_ne_zero (pow_ne_zero 2 C.u.ne_zero) (sub_ne_zero.mpr hx)
    field_simp [hd]
    ring

theorem forward_add (P Q : (C • W).toAffine.Point) :
    forward W C (P+Q) = forward W C P+forward W C Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      change forward W C ((Point.some x₁ y₁ h₁)+0) = forward W C (.some x₁ y₁ h₁)+0
      rw [add_zero,add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hv : x₁=x₂ ∧ y₁=(C • W).toAffine.negY x₂ y₂
      · rw [Point.add_of_Y_eq hv.1 hv.2]
        simp only [forward,Point.mk]
        have hv' := (vertical_iff W C x₁ x₂ y₁ y₂).mpr hv
        exact (Point.add_of_Y_eq hv'.1 hv'.2).symm
      · rw [Point.add_some hv]
        simp only [forward,Point.mk]
        rw [Point.add_some (mt (vertical_iff W C x₁ x₂ y₁ y₂).mp hv)]
        congr 1
        · rw [slope_change W C x₁ x₂ y₁ y₂ h₁.1 h₂.1 hv,addX_change]
        · rw [slope_change W C x₁ x₂ y₁ y₂ h₁.1 h₂.1 hv,addY_change]

/-- The additive equivalence induced by an admissible variable change.
Its forward affine coordinates are (u²x+r,u³y+u²sx+t). -/
def pointEquiv : (C • W).toAffine.Point ≃+ W.toAffine.Point where
  toFun := forward W C
  invFun := backward W C
  left_inv := backward_forward W C
  right_inv := forward_backward W C
  map_add' := forward_add W C

end
end Z2Z4Rank6.VariableChangePoints
