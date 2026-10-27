module

public import Z2Z4Rank6.SecondParameterSelectionSections

@[expose] public section

/-!
# Generic sections from the parameter equations

The generic twist is the printed Weierstrass curve over Q(W).
The excluded parameters are proved to be exactly those where its computed
twist constant vanishes. For all remaining parameters the generic
curve is elliptic and the prescribed section is a point of its group.
-/
namespace Z2Z4Rank6.SecondParameterSelection
noncomputable section

abbrev RF := RatFunc ℚ

def genericTwist (l b k : ℚ) : WeierstrassCurve RF :=
  twistedModel (RatFunc.C l) RatFunc.X (RatFunc.C k*(RatFunc.X-RatFunc.C b))

theorem parameter_sub_const_ne_zero (a : ℚ) : (RatFunc.X : RF)-RatFunc.C a≠0 := by
  intro h
  have he : algebraMap (Polynomial ℚ) RF (Polynomial.X-Polynomial.C a)=
      algebraMap (Polynomial ℚ) RF 0 := by
    simpa only [map_sub,RatFunc.algebraMap_X,RatFunc.algebraMap_C,map_zero] using h
  have hh := (IsFractionRing.injective (Polynomial ℚ) RF) he
  exact Polynomial.X_sub_C_ne_zero a hh

theorem genericTwist_elliptic (l b k : ℚ) (hl : l≠-1) (hk : k≠0) :
    (genericTwist l b k).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  have hkc : RatFunc.C k≠0 := by
    intro h
    apply hk
    apply RatFunc.C.injective
    simpa only [map_zero] using h
  have hq : RatFunc.C k*(RatFunc.X-RatFunc.C b)≠0 :=
    mul_ne_zero hkc (parameter_sub_const_ne_zero b)
  have hp : RatFunc.C l+1≠0 := by
    intro h
    have hh : RatFunc.C (l+1)=RatFunc.C 0 := by simpa only [map_add,map_one,map_zero] using h
    have hz := (RatFunc.C : ℚ →+* RF).injective hh
    apply hl
    linarith
  have h1 : (RatFunc.X : RF)-1≠0 := by simpa only [map_one] using parameter_sub_const_ne_zero 1
  have h2 : (RatFunc.X : RF)-(RatFunc.C l)^2≠0 := by
    have hc : RatFunc.C (l^2)=(RatFunc.C l : RF)^2 := map_pow (RatFunc.C : ℚ →+* RF) l 2
    rw [←hc]
    exact parameter_sub_const_ne_zero (l^2)
  have h3 : (RatFunc.X : RF)+RatFunc.C l≠0 := by
    simpa only [map_neg,sub_neg_eq_add] using parameter_sub_const_ne_zero (-l)
  rw [genericTwist,generic_discriminant]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 6 hq)) (pow_ne_zero 4 h1))
      (pow_ne_zero 4 h2)) (pow_ne_zero 2 hp)) RatFunc.X_ne_zero) (pow_ne_zero 2 h3)

theorem firstCondition_C (l b : ℚ) :
    firstCondition (RatFunc.C l) (RatFunc.C b)=RatFunc.C (firstCondition l b) := by
  simp only [firstCondition,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem secondCondition_C (l b : ℚ) :
    secondCondition (RatFunc.C l) (RatFunc.C b)=RatFunc.C (secondCondition l b) := by
  simp only [secondCondition,map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]

theorem firstMultiplier_C (l b : ℚ) :
    firstMultiplier (RatFunc.C l) (RatFunc.C b)=RatFunc.C (firstMultiplier l b) := by
  simp only [firstMultiplier,map_div₀,map_sub,map_pow,map_mul,map_ofNat,map_one]

theorem secondMultiplier_C (l b : ℚ) :
    secondMultiplier (RatFunc.C l) (RatFunc.C b)=RatFunc.C (secondMultiplier l b) := by
  simp only [secondMultiplier,secondNumerator,map_div₀,map_add,map_sub,map_pow,map_mul,
    map_ofNat,map_one]

/-- A point over Q(W) on the computed first twist, with the
prescribed x-coordinate a constant times (W-1)(W-lambda²). -/
def firstSection (l b : ℚ) (hl : l≠-1) (h : firstCondition l b=0)
    (hdeg : ¬(l=1 ∧ b=0)) :
    (genericTwist l b (firstMultiplier l b)).toAffine.Point := by
  letI := genericTwist_elliptic l b (firstMultiplier l b) hl
    (by intro hk; exact hdeg ((first_multiplier_zero l b hl h).mp hk))
  refine .mk (x:=firstX (RatFunc.C l) (RatFunc.C b) RatFunc.X)
    (y:=firstY (RatFunc.C l) (RatFunc.C b) RatFunc.X) ?_
  change (twistedModel (RatFunc.C l) RatFunc.X
    (RatFunc.C (firstMultiplier l b)*(RatFunc.X-RatFunc.C b))).toAffine.Equation _ _
  rw [←firstMultiplier_C]
  apply first_section_equation
  rw [firstCondition_C,h,map_zero]

/-- A point over Q(W) on the computed second twist, with the
prescribed x-coordinate a constant times (W-1)(W-beta). -/
def secondSection (l b : ℚ) (hl : l≠-1) (h : secondCondition l b=0)
    (hdeg : ¬(l=1 ∧ b=1)) :
    (genericTwist l b (secondMultiplier l b)).toAffine.Point := by
  letI := genericTwist_elliptic l b (secondMultiplier l b) hl
    (by intro hk; exact hdeg ((second_multiplier_zero l b hl h).mp hk))
  refine .mk (x:=secondX (RatFunc.C l) (RatFunc.C b) RatFunc.X)
    (y:=secondY (RatFunc.C l) (RatFunc.C b) RatFunc.X) ?_
  change (twistedModel (RatFunc.C l) RatFunc.X
    (RatFunc.C (secondMultiplier l b)*(RatFunc.X-RatFunc.C b))).toAffine.Equation _ _
  rw [←secondMultiplier_C]
  apply second_section_equation
  · intro hh
    apply hl
    apply RatFunc.C.injective
    simpa only [map_neg,map_one] using hh
  · rw [secondCondition_C,h,map_zero]

/-- The first generic point has precisely the prescribed coordinates. -/
theorem first_prescribed_section (l b : ℚ) (hl : l≠-1) (h : firstCondition l b=0)
    (hdeg : ¬(l=1 ∧ b=0)) :
    ∃ P : (genericTwist l b (firstMultiplier l b)).toAffine.Point,
      Common.WeierstrassCoordinates.encode P=
        some (firstX (RatFunc.C l) (RatFunc.C b) RatFunc.X,
          firstY (RatFunc.C l) (RatFunc.C b) RatFunc.X) :=
  ⟨firstSection l b hl h hdeg,rfl⟩

/-- The second generic point has precisely the prescribed coordinates. -/
theorem second_prescribed_section (l b : ℚ) (hl : l≠-1) (h : secondCondition l b=0)
    (hdeg : ¬(l=1 ∧ b=1)) :
    ∃ P : (genericTwist l b (secondMultiplier l b)).toAffine.Point,
      Common.WeierstrassCoordinates.encode P=
        some (secondX (RatFunc.C l) (RatFunc.C b) RatFunc.X,
          secondY (RatFunc.C l) (RatFunc.C b) RatFunc.X) :=
  ⟨secondSection l b hl h hdeg,rfl⟩

/-- Both computed twist polynomials differ from qA by explicit nonzero squares. -/
theorem chosen_twist_scalings (t : ℚ) :
    firstMultiplier SecondFamily.lambda SecondFamily.beta*(t-SecondFamily.beta)=
        (35/1089)^2*SecondFamily.qA t ∧
      secondMultiplier SecondFamily.lambda SecondFamily.beta*(t-SecondFamily.beta)=
        (32/1089)^2*SecondFamily.qA t := by
  rw [chosen_twist_constants.1,chosen_twist_constants.2]
  unfold SecondFamily.qA
  constructor <;> ring

/-- The computed generic sections become exactly the printed Q2 and Q3
under the displayed rational square scalings of their twists. -/
theorem chosen_coordinate_scalings (t : ℚ) :
    firstX SecondFamily.lambda SecondFamily.beta t=(35/1089)^2*SecondFamily.x2 t ∧
    firstY SecondFamily.lambda SecondFamily.beta t=(35/1089)^3*SecondFamily.y2 t ∧
    secondX SecondFamily.lambda SecondFamily.beta t=(32/1089)^2*SecondFamily.x3 t ∧
    secondY SecondFamily.lambda SecondFamily.beta t=(32/1089)^3*SecondFamily.y3 t := by
  norm_num [firstX,firstY,firstSquare,firstMultiplier,secondX,secondY,secondRoot,
    secondMultiplier,secondNumerator,SecondFamily.lambda,SecondFamily.beta,
    SecondFamily.x2,SecondFamily.y2,SecondFamily.f2,SecondFamily.x3,SecondFamily.y3]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end
end Z2Z4Rank6.SecondParameterSelection
