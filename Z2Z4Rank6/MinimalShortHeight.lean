module

public import Z2Z4Rank6.ShortPrimitiveUniqueness
public import Z2Z4Rank6.Basic
public import Z2Z4Rank6.VariableChangePoints

@[expose] public section

/-!
# Short equations and the normalized coefficient height

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3 (height), uses primitive
integer short coefficients. We construct the admissible change
and point-group equivalence, and keep the twelfth-power normalization
factor explicit. Short primitivity is not asserted to be global minimality
among arbitrary integral long Weierstrass equations.
-/
namespace Z2Z4Rank6.ShortHeight
open WeierstrassCurve
noncomputable section
open scoped Classical

def shortCurve {R : Type*} [CommRing R] (A B : R) : WeierstrassCurve R :=
  ⟨0,0,0,A,B⟩

theorem shortCurve_discriminant {R : Type*} [CommRing R] (A B : R) :
    (shortCurve A B).Δ= -16*(4*A^3+27*B^2) := by
  simp only [shortCurve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem nonzero_pair_of_nonsingular (A B : ℤ) (h : 4*A^3+27*B^2≠0) : A≠0∨B≠0 := by
  by_contra hab
  push Not at hab
  simp [hab.1,hab.2] at h

theorem exists_normalization_of_nonsingular (A B : ℤ) (h : 4*A^3+27*B^2≠0) :
    Nonempty (Normalization A B) :=
  ⟨normalization A B (nonzero_pair_of_nonsingular A B h)⟩

def Normalization.change {A B : ℤ} (n : Normalization A B) : VariableChange ℚ :=
  ⟨Units.mk0 (n.scale:ℚ) (by exact_mod_cast (Nat.ne_zero_of_lt n.scale_pos)),0,0,0⟩

/-- The fourth/sixth normalization is an admissible coordinate change. -/
theorem Normalization.change_eq {A B : ℤ} (n : Normalization A B) :
    n.change • shortCurve (A:ℚ) (B:ℚ)=shortCurve (n.shortA:ℚ) (n.shortB:ℚ) := by
  have hd : (n.scale:ℚ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt n.scale_pos)
  have hA : (A:ℚ)=(n.scale:ℚ)^4*(n.shortA:ℚ) := by exact_mod_cast n.eqA
  have hB : (B:ℚ)=(n.scale:ℚ)^6*(n.shortB:ℚ) := by exact_mod_cast n.eqB
  ext <;> norm_num [Normalization.change,shortCurve,variableChange_def,hA,hB]
  all_goals field_simp [hd]

/-- Additive equivalence between the normalized short model and
the original short model, including the point at infinity. -/
def Normalization.pointEquiv {A B : ℤ} (n : Normalization A B)
    [(shortCurve (A:ℚ) (B:ℚ)).IsElliptic] :
    (shortCurve (n.shortA:ℚ) (n.shortB:ℚ)).toAffine.Point ≃+
      (shortCurve (A:ℚ) (B:ℚ)).toAffine.Point :=
  (PointScaling.pointCongr n.change_eq.symm).trans
    (VariableChangePoints.pointEquiv _ n.change)

/-- Clearing the cubic-translation denominators gives integral short A. -/
def integralShortA (V : WeierstrassCurve ℤ) : ℤ := -27*V.c₄
/-- The matching integral short B. -/
def integralShortB (V : WeierstrassCurve ℤ) : ℤ := -54*V.c₆

/-- The change for a₁=a₃=0: u=1/6,r=−a₂/3,s=t=0. -/
def integralShortChange (W : WeierstrassCurve ℚ) : VariableChange ℚ :=
  ⟨Units.mk0 (1/6:ℚ) (by norm_num),-W.a₂/3,0,0⟩

theorem integralShortChange_eq (W : WeierstrassCurve ℚ) (h1 : W.a₁=0) (h3 : W.a₃=0) :
    integralShortChange W • W=shortCurve (-27*W.c₄) (-54*W.c₆) := by
  ext <;> norm_num [integralShortChange,shortCurve,variableChange_def,
    WeierstrassCurve.c₄,WeierstrassCurve.c₆,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,h1,h3] <;> ring

theorem integer_integralShortChange_eq (V : WeierstrassCurve ℤ)
    (h1 : V.a₁=0) (h3 : V.a₃=0) :
    integralShortChange (V.map (Int.castRingHom ℚ)) • V.map (Int.castRingHom ℚ)=
      shortCurve (integralShortA V : ℚ) (integralShortB V : ℚ) := by
  have h := integralShortChange_eq (V.map (Int.castRingHom ℚ))
    (by simp only [map_a₁,h1,map_zero]) (by simp only [map_a₃,h3,map_zero])
  simpa only [integralShortA,integralShortB,map_c₄,map_c₆,Int.cast_mul,Int.cast_neg,
    Int.cast_ofNat,Int.coe_castRingHom] using h

/-- The integral long-to-short change acts on the point groups. -/
def integralShortPointEquiv (V : WeierstrassCurve ℤ) (h1 : V.a₁=0) (h3 : V.a₃=0)
    [(V.map (Int.castRingHom ℚ)).IsElliptic] :
    (shortCurve (integralShortA V : ℚ) (integralShortB V : ℚ)).toAffine.Point ≃+
      (V.map (Int.castRingHom ℚ)).toAffine.Point :=
  (PointScaling.pointCongr (integer_integralShortChange_eq V h1 h3).symm).trans
    (VariableChangePoints.pointEquiv _ (integralShortChange _))

/-- The integral short equation is elliptic whenever its original
long equation is elliptic. -/
theorem integralShort_isElliptic (V : WeierstrassCurve ℤ) (h1 : V.a₁=0) (h3 : V.a₃=0)
    [(V.map (Int.castRingHom ℚ)).IsElliptic] :
    (shortCurve (integralShortA V : ℚ) (integralShortB V : ℚ)).IsElliptic := by
  rw [←integer_integralShortChange_eq V h1 h3]
  infer_instance

/-- Nonsingularity rules out the zero short-coefficient pair, allowing the
finite positive-scale normalization theorem to be applied. -/
theorem integralShort_nonzero (V : WeierstrassCurve ℤ) (h1 : V.a₁=0) (h3 : V.a₃=0)
    [(V.map (Int.castRingHom ℚ)).IsElliptic] : integralShortA V≠0∨integralShortB V≠0 := by
  let := integralShort_isElliptic V h1 h3
  have hd : (shortCurve (integralShortA V : ℚ) (integralShortB V : ℚ)).Δ≠0 :=
    isUnit_iff_ne_zero.mp (WeierstrassCurve.IsElliptic.isUnit)
  by_contra hab
  push Not at hab
  simp [shortCurve_discriminant,hab.1,hab.2] at hd

/-- The primitive normalized short equation and the original integral long
equation have an additive point-group equivalence. -/
def normalizedIntegralShortPointEquiv (V : WeierstrassCurve ℤ)
    (h1 : V.a₁=0) (h3 : V.a₃=0) [(V.map (Int.castRingHom ℚ)).IsElliptic]
    (n : Normalization (integralShortA V) (integralShortB V)) :
    (shortCurve (n.shortA:ℚ) (n.shortB:ℚ)).toAffine.Point ≃+
      (V.map (Int.castRingHom ℚ)).toAffine.Point := by
  letI := integralShort_isElliptic V h1 h3
  exact n.pointEquiv.trans (integralShortPointEquiv V h1 h3)

/-- Raw short height in terms of the integral long equation's invariants.
The primitive height still differs by the explicit normalization's
scale to the twelfth power. -/
theorem integralShortHeight_eq (V : WeierstrassCurve ℤ) :
    coefficientHeight (integralShortA V) (integralShortB V)=
      78732*max (V.c₄.natAbs^3) (V.c₆.natAbs^2) := by
  have h4 : 4*(integralShortA V).natAbs^3=78732*V.c₄.natAbs^3 := by
    simp only [integralShortA,Int.natAbs_mul,Int.natAbs_neg,mul_pow]
    ring
  have h6 : 27*(integralShortB V).natAbs^2=78732*V.c₆.natAbs^2 := by
    simp only [integralShortB,Int.natAbs_mul,Int.natAbs_neg,mul_pow]
    ring
  simp only [coefficientHeight,h4,h6,←mul_max]

/-- Exact integral short coefficients for the paper's first family. -/
theorem E_integralShort_coefficients (a b : ℤ) :
    integralShortA (E a b)= -432*(a^4-a^2*b^2+b^4) ∧
    integralShortB (E a b)=1728*(a^2+b^2)*(2*a^4-5*a^2*b^2+2*b^4) := by
  constructor <;> norm_num [integralShortA,integralShortB,E,WeierstrassCurve.c₄,
    WeierstrassCurve.c₆,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆] <;> ring

/-- Every admissible change between short equations is a pure scale. -/
theorem variableChange_between_short (A B A0 B0 : ℚ) (C : VariableChange ℚ)
    (h : C • shortCurve A B=shortCurve A0 B0) :
    C.r=0 ∧ C.s=0 ∧ C.t=0 ∧
      A0=(C.u:ℚ)⁻¹^4*A ∧ B0=(C.u:ℚ)⁻¹^6*B := by
  have hs : C.s=0 := by
    have h1 := congrArg (fun W : WeierstrassCurve ℚ => W.a₁) h
    simpa [variableChange_a₁,shortCurve,mul_eq_zero] using h1
  have hr : C.r=0 := by
    have h2 := congrArg (fun W : WeierstrassCurve ℚ => W.a₂) h
    simpa [variableChange_a₂,shortCurve,hs,mul_eq_zero] using h2
  have ht : C.t=0 := by
    have h3 := congrArg (fun W : WeierstrassCurve ℚ => W.a₃) h
    simpa [variableChange_a₃,shortCurve,hr,mul_eq_zero] using h3
  refine ⟨hr,hs,ht,?_,?_⟩
  · have h4 := congrArg (fun W : WeierstrassCurve ℚ => W.a₄) h
    simpa [variableChange_a₄,shortCurve,hr,hs,ht] using h4.symm
  · have h6 := congrArg (fun W : WeierstrassCurve ℚ => W.a₆) h
    simpa [variableChange_a₆,shortCurve,hr,hs,ht] using h6.symm

/-- Primitive integral short equations related by an admissible
rational Weierstrass isomorphism have identical coefficients. -/
theorem primitive_short_models_unique (A B A0 B0 : ℤ)
    (hp : ShortPrimitive A B) (hp0 : ShortPrimitive A0 B0)
    (C : VariableChange ℚ)
    (h : C • shortCurve (A:ℚ) (B:ℚ)=shortCurve (A0:ℚ) (B0:ℚ)) : A=A0∧B=B0 := by
  obtain ⟨_,_,_,h4,h6⟩ := variableChange_between_short _ _ _ _ C h
  have hc := primitive_coefficients_eq_of_rational_scale (C.u:ℚ)⁻¹
    (inv_ne_zero C.u.ne_zero) A0 B0 A B h4 h6 hp0 hp
  exact ⟨hc.1.symm,hc.2.symm⟩

/-- The paper's primitive-short height is invariant under admissible
rational isomorphisms between primitive short equations. -/
theorem primitive_short_height_invariant (A B A0 B0 : ℤ)
    (hp : ShortPrimitive A B) (hp0 : ShortPrimitive A0 B0)
    (C : VariableChange ℚ)
    (h : C • shortCurve (A:ℚ) (B:ℚ)=shortCurve (A0:ℚ) (B0:ℚ)) :
    coefficientHeight A B=coefficientHeight A0 B0 := by
  obtain ⟨rfl,rfl⟩ := primitive_short_models_unique A B A0 B0 hp hp0 C h
  rfl

/-- A primitive pair cannot be identically zero. -/
theorem ShortPrimitive.nonzero_pair {A B : ℤ} (hp : ShortPrimitive A B) : A≠0∨B≠0 := by
  by_contra hz
  push Not at hz
  apply hp 2 (by decide)
  exact ⟨by rw [hz.1];exact dvd_zero _,by rw [hz.2];exact dvd_zero _⟩

theorem coefficientHeight_pos (A B : ℤ) (hn : A≠0∨B≠0) : 0<coefficientHeight A B := by
  rcases hn with hA | hB
  · exact (Nat.mul_pos (by decide) (pow_pos (Int.natAbs_pos.mpr hA) 3)).trans_le (le_max_left _ _)
  · exact (Nat.mul_pos (by decide) (pow_pos (Int.natAbs_pos.mpr hB) 2)).trans_le (le_max_right _ _)

theorem Normalization.height_pos {A B : ℤ} (n : Normalization A B) : 0<n.height :=
  coefficientHeight_pos _ _ n.primitive.nonzero_pair

/-- A bound on the removable twelfth-power scale turns the exact raw-height
identity into both needed integer height comparisons. -/
theorem Normalization.height_bounds {A B : ℤ} (n : Normalization A B) (C : ℕ)
    (hC : n.scale^12≤C) :
    n.height≤coefficientHeight A B ∧ coefficientHeight A B≤C*n.height := by
  have hd : 1≤n.scale^12 := Nat.succ_le_iff.mpr (pow_pos n.scale_pos 12)
  constructor
  · calc
      n.height=1*n.height := by omega
      _≤n.scale^12*n.height := Nat.mul_le_mul_right _ hd
      _=coefficientHeight A B := n.rawHeight_eq.symm
  · rw [n.rawHeight_eq]
    exact Nat.mul_le_mul_right _ hC

end
end Z2Z4Rank6.ShortHeight
