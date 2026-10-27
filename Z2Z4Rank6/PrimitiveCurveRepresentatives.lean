import Z2Z4Rank6.MinimalShortHeight
import Z2Z4Rank6.FiniteImageCounting

/-!
# Primitive short coefficient pairs as curve representatives

The pair (A,B) represents y²=x³+Ax+B, with the primitive condition used
in Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117, and Park--Poonen--Voight--Wood,
JEMS 21 (2019), §5.1. Equality of primitive pairs is equivalent to a
rational admissible Weierstrass change between their represented equations.
The usual extended j formula factors through the coefficient pair; no
height is assigned to a j-invariant.
-/
namespace Z2Z4Rank6.PrimitiveCurveRepresentatives
open WeierstrassCurve ShortHeight
noncomputable section

abbrev Coefficients := ℤ×ℤ

def model (r : Coefficients) : WeierstrassCurve ℚ := shortCurve (r.1:ℚ) (r.2:ℚ)
def height (r : Coefficients) : ℕ := coefficientHeight r.1 r.2
def j (r : Coefficients) : ℚ := jValue (model r)

theorem model_injective : Function.Injective model := by
  intro r s hrs
  apply Prod.ext
  · have h := congrArg (fun W : WeierstrassCurve ℚ => W.a₄) hrs
    change (r.1:ℚ)=(s.1:ℚ) at h
    exact_mod_cast h
  · have h := congrArg (fun W : WeierstrassCurve ℚ => W.a₆) hrs
    change (r.2:ℚ)=(s.2:ℚ) at h
    exact_mod_cast h

/-- The extended j formula is invariant under every admissible
change, including at singular equations where its inverse convention is 0. -/
theorem jValue_variableChange (W : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    jValue (C • W)=jValue W := by
  simp only [jValue,variableChange_Δ,variableChange_c₄,mul_pow,←pow_mul,
    Units.val_inv_eq_inv_val]
  change ((C.u:ℚ)⁻¹^12*W.Δ)⁻¹*((C.u:ℚ)⁻¹^(4*3)*W.c₄^3)=W.Δ⁻¹*W.c₄^3
  norm_num only [Nat.reduceMul]
  rw [mul_inv_rev]
  calc
    _=W.Δ⁻¹*((C.u:ℚ)⁻¹^12)⁻¹*((C.u:ℚ)⁻¹^12)*W.c₄^3 := by ring
    _=W.Δ⁻¹*W.c₄^3 := by
      rw [mul_assoc W.Δ⁻¹,inv_mul_cancel₀ (pow_ne_zero _ (inv_ne_zero C.u.ne_zero)),mul_one]

theorem j_factorization (W : WeierstrassCurve ℚ) (r : Coefficients)
    (C : VariableChange ℚ) (hC : C • W=model r) : jValue W=j r := by
  rw [j,←hC,jValue_variableChange]

/-- Any two primitive short representatives coincide exactly when
their source equations are related by an admissible rational change. -/
theorem coefficients_eq_iff_exists_change (W V : WeierstrassCurve ℚ)
    (r s : Coefficients) (hr : ShortPrimitive r.1 r.2) (hs : ShortPrimitive s.1 s.2)
    (C D : VariableChange ℚ) (hC : C • W=model r) (hD : D • V=model s) :
    r=s ↔ ∃e : VariableChange ℚ,e • W=V := by
  constructor
  · intro hrs
    refine ⟨D⁻¹*C,?_⟩
    rw [mul_smul,hC,hrs,←hD,inv_smul_smul]
  · rintro ⟨e,he⟩
    have h : (D*e*C⁻¹) • model r=model s := by
      rw [mul_smul,mul_smul,←hC,inv_smul_smul,he,hD]
    exact Prod.ext (primitive_short_models_unique _ _ _ _ hr hs _ h).1
      (primitive_short_models_unique _ _ _ _ hr hs _ h).2

/-- Admissible changes preserve the exact torsion and six-point
independence property, using the already proved point-group equivalence. -/
theorem desiredCurve_of_change (W V : WeierstrassCurve ℚ) (C : VariableChange ℚ)
    (hC : C • W=V) (hW : DesiredCurve W) : DesiredCurve V := by
  let := hW.1
  have hV : GoodCurve V := by
    rw [←hC]
    infer_instance
  let e : RationalPoints V≃+RationalPoints W :=
    (PointScaling.pointCongr hC.symm).trans (VariableChangePoints.pointEquiv W C)
  refine ⟨hV,?_,?_⟩
  · obtain ⟨t⟩ := hW.2.1
    exact ⟨((e.addSubgroupMap _).trans (AddEquiv.addSubgroupCongr e.map_torsion)).trans t⟩
  · obtain ⟨P,hP⟩ := hW.2.2
    exact ⟨fun i => e.symm (P i),hP.map' e.symm.toIntLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.symm.injective)⟩

/-- A fixed factorization through a refined representative can only make
fibers smaller. This is the finite-cardinality part of the curve/j bridge. -/
theorem ncard_le_mul_ncard_refined_image {α β γ : Type*} (S : Set α) (hS : S.Finite)
    (r : α→β) (f : α→γ) (g : β→γ) (hfactor : ∀a,f a=g (r a)) (n : ℕ)
    (hbound : S.ncard≤n*(f '' S).ncard) : S.ncard≤n*(r '' S).ncard := by
  have himage : f '' S=g '' (r '' S) := by
    ext z
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨r a,⟨a,ha,rfl⟩,(hfactor a).symm⟩
    · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
      exact ⟨a,ha,hfactor a⟩
  rw [himage] at hbound
  exact hbound.trans (Nat.mul_le_mul_left n (Set.ncard_image_le (hS.image r)))

end
end Z2Z4Rank6.PrimitiveCurveRepresentatives
