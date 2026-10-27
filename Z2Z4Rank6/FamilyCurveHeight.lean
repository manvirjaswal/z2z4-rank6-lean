import Z2Z4Rank6.MinimalShortHeight
import Z2Z4Rank6.HeightInvariantBounds
import Z2Z4Rank6.HeightInvariantContent
import Z2Z4Rank6.NeronRigidCounting
import Z2Z4Rank6.FamilyIdentities

/-!
# Primitive-short height for every rational first-family parameter

Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3 (height). The rational parameter
is represented by its reduced pair (denominator,numerator). We
normalize the integral short equation, prove its point-group
equivalence to X at smooth parameters, and prove height comparison with
the 48th power of the reduced rational parameter height.
-/
namespace Z2Z4Rank6.FamilyCurveHeight
open WeierstrassCurve
open ShortHeight
noncomputable section
open scoped Classical

/-- Integral binary model at the reduced rational parameter pair. -/
def binaryIntegralModel (q : ℚ) : WeierstrassCurve ℤ :=
  HeightInvariantForms.binaryModel (q.den:ℤ) q.num

def rawShortA (q : ℚ) : ℤ := integralShortA (binaryIntegralModel q)
def rawShortB (q : ℚ) : ℤ := integralShortB (binaryIntegralModel q)

/-- The reduced pair is primitive with denominator coordinate first. -/
theorem parameter_pair_coprime (q : ℚ) : Nat.Coprime (q.den:ℤ).natAbs q.num.natAbs := by
  simpa only [Int.natAbs_natCast] using q.reduced.symm

theorem binaryModel_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x0 x1 : R) :
    (HeightInvariantForms.binaryModel x0 x1).map f=
      HeightInvariantForms.binaryModel (f x0) (f x1) := by
  ext <;> simp [HeightInvariantForms.binaryModel,E,HeightInvariantForms.binaryA,
    HeightInvariantForms.binaryB,map_ofNat]

theorem c4_intCast {S : Type*} [CommRing S] (x0 x1 : ℤ) :
    ((HeightInvariantForms.c4 x0 x1:ℤ):S)=HeightInvariantForms.c4 (x0:S) (x1:S) := by
  have h := congrArg (fun V : WeierstrassCurve S => V.c₄)
    (binaryModel_map (Int.castRingHom S) x0 x1)
  simpa only [map_c₄,Int.coe_castRingHom,HeightInvariantForms.c4] using h

theorem c6_intCast {S : Type*} [CommRing S] (x0 x1 : ℤ) :
    ((HeightInvariantForms.c6 x0 x1:ℤ):S)=HeightInvariantForms.c6 (x0:S) (x1:S) := by
  have h := congrArg (fun V : WeierstrassCurve S => V.c₆)
    (binaryModel_map (Int.castRingHom S) x0 x1)
  simpa only [map_c₆,Int.coe_castRingHom,HeightInvariantForms.c6] using h

/-- The short pair is nonzero even at the finitely many singular parameters;
this numerical extension is not asserted to be elliptic there. -/
theorem raw_pair_nonzero (q : ℚ) : rawShortA q≠0∨rawShortB q≠0 := by
  by_contra hz
  push Not at hz
  have h4Z : HeightInvariantForms.c4 (q.den:ℤ) q.num=0 := by
    have h4 : (-27:ℤ)*HeightInvariantForms.c4 (q.den:ℤ) q.num=0 := hz.1
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  have h6Z : HeightInvariantForms.c6 (q.den:ℤ) q.num=0 := by
    have h6 : (-54:ℤ)*HeightInvariantForms.c6 (q.den:ℤ) q.num=0 := hz.2
    exact (mul_eq_zero.mp h6).resolve_left (by norm_num)
  have h4 := c4_intCast (S:=ℚ) (q.den:ℤ) q.num
  have h6 := c6_intCast (S:=ℚ) (q.den:ℤ) q.num
  simp only [h4Z,h6Z,Int.cast_zero,Int.cast_natCast] at h4 h6
  apply HeightInvariantForms.invariants_not_both_zero (q.den:ℚ) (q.num:ℚ)
    (Or.inl (by exact_mod_cast (Nat.ne_zero_of_lt q.den_pos)))
  exact ⟨h4.symm,h6.symm⟩

/-- Positive-scale primitive short normalization, for every q. -/
def normalization (q : ℚ) : ShortHeight.Normalization (rawShortA q) (rawShortB q) :=
  ShortHeight.normalization _ _ (raw_pair_nonzero q)

def normalizedModel (q : ℚ) : WeierstrassCurve ℚ :=
  shortCurve ((normalization q).shortA:ℚ) ((normalization q).shortB:ℚ)

/-- The paper's height on the primitive integer short representative.
At singular parameters this is only the same coefficient-height extension. -/
def height (q : ℚ) : ℕ := (normalization q).height

def rawHeight (q : ℚ) : ℕ := coefficientHeight (rawShortA q) (rawShortB q)

theorem normalized_primitive (q : ℚ) :
    ShortPrimitive (normalization q).shortA (normalization q).shortB := (normalization q).primitive

theorem height_pos (q : ℚ) : 0<height q := (normalization q).height_pos

theorem height_eq_paper (q : ℚ) :
    height q=max (4*(normalization q).shortA^3).natAbs
      (27*(normalization q).shortB^2).natAbs := coefficientHeight_eq _ _

theorem rawHeight_eq (q : ℚ) : rawHeight q=(normalization q).scale^12*height q :=
  (normalization q).rawHeight_eq

/-- Every normalization scale is uniformly bounded, using the proved
binary invariant content certificate at the reduced primitive pair. -/
theorem normalization_scales_bounded :
    ∃ C : ℕ,0<C ∧ ∀ q : ℚ,(normalization q).scale^12≤C := by
  obtain ⟨C,hC,h⟩ := HeightInvariantContent.exists_normalization_bound
  refine ⟨C,hC,?_⟩
  intro q
  exact h (q.den:ℤ) q.num (parameter_pair_coprime q) (normalization q).scale
    ⟨(normalization q).shortA,(normalization q).eqA⟩
    ⟨(normalization q).shortB,(normalization q).eqB⟩

/-- Exact relation between the raw integral-short height and the
binary invariant size over the reals. -/
theorem rawHeight_real (q : ℚ) :
    (rawHeight q:ℝ)=78732*HeightInvariantForms.rawHeight ((q.den:ℝ),(q.num:ℝ)) := by
  have hNat : rawHeight q=78732*max
      ((HeightInvariantForms.c4 (q.den:ℤ) q.num).natAbs^3)
      ((HeightInvariantForms.c6 (q.den:ℤ) q.num).natAbs^2) :=
    integralShortHeight_eq (binaryIntegralModel q)
  have hR := congrArg (fun n : ℕ => (n:ℝ)) hNat
  have h4 := c4_intCast (S:=ℝ) (q.den:ℤ) q.num
  have h6 := c6_intCast (S:=ℝ) (q.den:ℤ) q.num
  simp only [Int.cast_natCast] at h4 h6
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_max,Nat.cast_pow,Nat.cast_natAbs,
    Int.cast_abs,h4,h6,HeightInvariantForms.rawHeight] using hR

theorem parameterHeight_real (q : ℚ) :
    max |(q.den:ℝ)| |(q.num:ℝ)|=(rationalParameterHeight q:ℝ) := by
  simp [rationalParameterHeight,Nat.cast_max,Nat.cast_natAbs,Int.cast_abs,max_comm]

/-- The normalized primitive-short height has the 48th-power growth
claimed in Remark 6.3, uniformly for every rational parameter. -/
theorem height_bounds : ∃ L U : ℝ,0<L ∧ 0<U ∧ ∀ q : ℚ,
    L*(rationalParameterHeight q:ℝ)^48≤(height q:ℝ) ∧
      (height q:ℝ)≤U*(rationalParameterHeight q:ℝ)^48 := by
  obtain ⟨C,hC,hscale⟩ := normalization_scales_bounded
  obtain ⟨L,U,hL,hU,hraw⟩ := HeightInvariantForms.rawHeight_bounds
  have hCR : (0:ℝ)<C := by exact_mod_cast hC
  refine ⟨78732*L/C,78732*U,div_pos (mul_pos (by norm_num) hL) hCR,
    mul_pos (by norm_num) hU,?_⟩
  intro q
  have hrawq := hraw (q.den:ℝ) (q.num:ℝ)
  rw [parameterHeight_real] at hrawq
  have hb := (normalization q).height_bounds C (hscale q)
  have hnormlo : (height q:ℝ)≤(rawHeight q:ℝ) := by exact_mod_cast hb.1
  have hnormhi : (rawHeight q:ℝ)≤(C:ℝ)*(height q:ℝ) := by exact_mod_cast hb.2
  rw [rawHeight_real] at hnormlo hnormhi
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hCR).mpr
    nlinarith [hrawq.1]
  · nlinarith [hrawq.2]

/-- Coordinate scale from the rational model to the integral binary
model. Its u-coordinate is den(q)⁻⁴. -/
def binaryScale (q : ℚ) : VariableChange ℚ :=
  scalingChange (Units.mk0 ((q.den:ℚ)^4)
    (pow_ne_zero 4 (by exact_mod_cast (Nat.ne_zero_of_lt q.den_pos))))

theorem binaryScale_eq (q : ℚ) :
    binaryScale q • X q=(binaryIntegralModel q).map (Int.castRingHom ℚ) := by
  have hd : (q.den:ℚ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt q.den_pos)
  have hq : (q.num:ℚ)/(q.den:ℚ)=q := Rat.num_div_den q
  calc
    binaryScale q • X q=E ((q.den:ℚ)^4*a q) ((q.den:ℚ)^4*b q) := by
      simpa only [binaryScale,X,Units.val_mk0] using
        scalingChange_E (Units.mk0 ((q.den:ℚ)^4) (pow_ne_zero 4 hd)) (a q) (b q)
    _=HeightInvariantForms.binaryModel (q.den:ℚ) (q.num:ℚ) := by
      rw [HeightInvariantForms.binaryModel,HeightInvariantForms.binaryA_affine _ _ hd,
        HeightInvariantForms.binaryB_affine _ _ hd,hq]
    _=(binaryIntegralModel q).map (Int.castRingHom ℚ) := by
      rw [binaryIntegralModel,binaryModel_map]
      simp only [Int.coe_castRingHom,Int.cast_natCast]

/-- Additive equivalence of the integral binary model and X_q. -/
def binaryPointEquiv (q : ℚ) [(X q).IsElliptic] :
    ((binaryIntegralModel q).map (Int.castRingHom ℚ)).toAffine.Point ≃+ (X q).toAffine.Point :=
  (PointScaling.pointCongr (binaryScale_eq q).symm).trans
    (VariableChangePoints.pointEquiv _ (binaryScale q))

theorem binaryModel_isElliptic (q : ℚ) [(X q).IsElliptic] :
    ((binaryIntegralModel q).map (Int.castRingHom ℚ)).IsElliptic := by
  rw [←binaryScale_eq]
  infer_instance

/-- At every smooth rational parameter, the primitive short representative
has the elliptic point group of the original fiber X_q. -/
def pointEquiv (q : ℚ) [(X q).IsElliptic] :
    (normalizedModel q).toAffine.Point ≃+ (X q).toAffine.Point := by
  letI := binaryModel_isElliptic q
  exact (normalizedIntegralShortPointEquiv (binaryIntegralModel q) rfl rfl
    (normalization q)).trans (binaryPointEquiv q)

theorem normalizedModel_isElliptic (q : ℚ) [(X q).IsElliptic] : (normalizedModel q).IsElliptic := by
  let := binaryModel_isElliptic q
  let : (shortCurve (rawShortA q:ℚ) (rawShortB q:ℚ)).IsElliptic :=
    integralShort_isElliptic (binaryIntegralModel q) rfl rfl
  change (shortCurve ((normalization q).shortA:ℚ) ((normalization q).shortB:ℚ)).IsElliptic
  rw [←(normalization q).change_eq]
  infer_instance

/-- The complete admissible change from X_q to its primitive short
representative, with all three scaling/translation stages explicit. -/
def modelChange (q : ℚ) : VariableChange ℚ :=
  (normalization q).change *
    integralShortChange ((binaryIntegralModel q).map (Int.castRingHom ℚ)) * binaryScale q

theorem modelChange_eq (q : ℚ) : modelChange q • X q=normalizedModel q := by
  simp only [modelChange,mul_smul,binaryScale_eq]
  rw [integer_integralShortChange_eq (binaryIntegralModel q) rfl rfl]
  exact (normalization q).change_eq

/-- The height is constant under admissible rational isomorphisms
between fibers: their primitive short representatives have equal coefficients. -/
theorem height_invariant (q r : ℚ) (C : VariableChange ℚ) (h : C • X q=X r) :
    height q=height r := by
  let D := modelChange r*C*(modelChange q)⁻¹
  have hD : D • normalizedModel q=normalizedModel r := by
    dsimp only [D]
    rw [mul_smul,mul_smul,←modelChange_eq q,inv_smul_smul,h,modelChange_eq]
  exact primitive_short_height_invariant _ _ _ _ (normalization q).primitive
    (normalization r).primitive D hD

end
end Z2Z4Rank6.FamilyCurveHeight
