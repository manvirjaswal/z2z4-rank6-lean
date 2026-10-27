module

public import Z2Z4Rank6.PrimitiveCurveRepresentatives
public import Z2Z4Rank6.FirstHeightRemark

@[expose] public section

/-!
# Distinct primitive-short first-family curves at bounded curve height

Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117. We count the
primitive integer short coefficient pairs of smooth family fibers. Their
height is exactly max(|4A³|,|27B²|). Equality of representatives is
equivalent to a rational admissible change between family fibers;
the counted object is a curve representative rather than a j-value with
a bounded-height witness. Fixed j factorization bounds each
representative fiber by 192 and gives logarithmic exponent 1/2.
-/
namespace Z2Z4Rank6.FirstCurveRepresentativeCounting
open WeierstrassCurve FirstCurveHeightCounting
open PrimitiveCurveRepresentatives
noncomputable section

def representative (c : CPoint) : Coefficients :=
  ((FamilyCurveHeight.normalization c.m).shortA,(FamilyCurveHeight.normalization c.m).shortB)

theorem representative_primitive (c : CPoint) :
    ShortHeight.ShortPrimitive (representative c).1 (representative c).2 :=
  FamilyCurveHeight.normalized_primitive c.m

theorem representative_model_change (c : CPoint) :
    FamilyCurveHeight.modelChange c.m • X c.m=model (representative c) :=
  FamilyCurveHeight.modelChange_eq c.m

theorem representative_eq_iff (c d : CPoint) :
    representative c=representative d ↔ ∃C : VariableChange ℚ,C • X c.m=X d.m :=
  coefficients_eq_iff_exists_change _ _ _ _ (representative_primitive c)
    (representative_primitive d) _ _ (representative_model_change c) (representative_model_change d)

theorem j_factorization (c : CPoint) : jValue (X c.m)=j (representative c) :=
  PrimitiveCurveRepresentatives.j_factorization _ _ _ (representative_model_change c)

theorem height_factorization (c : CPoint) :
    PrimitiveCurveRepresentatives.height (representative c)=curveHeight c := rfl

theorem representative_good (c : CPoint) (hc : GoodCurve (X c.m)) :
    GoodCurve (model (representative c)) := by
  let := hc
  exact FamilyCurveHeight.normalizedModel_isElliptic c.m

/-- Every smooth representative fiber is contained in one fixed
j-fiber, so it is finite. -/
theorem finite_representative_fiber (r : Coefficients) :
    {c : CPoint | GoodCurve (X c.m) ∧ representative c=r}.Finite := by
  apply (finite_j_CPoint_fiber (j r)).subset
  rintro c ⟨hc,hr⟩
  exact ⟨hc,(j_factorization c).trans (congrArg j hr)⟩

theorem ncard_representative_fiber_le (r : Coefficients) :
    {c : CPoint | GoodCurve (X c.m) ∧ representative c=r}.ncard≤192 :=
  (Set.ncard_le_ncard (fun c hc =>
    ⟨hc.1,(j_factorization c).trans (congrArg j hc.2)⟩ :
      {c : CPoint | GoodCurve (X c.m) ∧ representative c=r}⊆
        {c : CPoint | GoodCurve (X c.m) ∧ jValue (X c.m)=j r})
    (finite_j_CPoint_fiber (j r))).trans (ncard_j_CPoint_fiber_le (j r))

def curveSet (S : Set CPoint) (H : ℕ) : Set Coefficients :=
  representative '' (heightSet H∩S)

def curveCount (S : Set CPoint) (H : ℕ) : ℕ := (curveSet S H).ncard

theorem mem_curveSet_iff (S : Set CPoint) (H : ℕ) (r : Coefficients) :
    r∈curveSet S H ↔ ∃c∈S,representative c=r ∧ PrimitiveCurveRepresentatives.height r≤H := by
  constructor
  · rintro ⟨c,⟨hc,hS⟩,rfl⟩
    exact ⟨c,hS,rfl,hc⟩
  · rintro ⟨c,hS,hr,hH⟩
    refine ⟨c,⟨?_,hS⟩,hr⟩
    rw [←hr] at hH
    exact hH

/-- An exact interpretation as primitive short equations of bounded height
admissibly isomorphic to a fiber with its base point in S. -/
theorem mem_curveSet_iff_model (S : Set CPoint) (H : ℕ) (r : Coefficients) :
    r∈curveSet S H ↔ ShortHeight.ShortPrimitive r.1 r.2 ∧
      PrimitiveCurveRepresentatives.height r≤H ∧
      ∃c∈S,∃C : VariableChange ℚ,C • X c.m=model r := by
  rw [mem_curveSet_iff]
  constructor
  · rintro ⟨c,hS,rfl,hH⟩
    exact ⟨representative_primitive c,hH,c,hS,_,representative_model_change c⟩
  · rintro ⟨hp,hH,c,hS,C,hC⟩
    have hr : representative c=r :=
      (coefficients_eq_iff_exists_change (X c.m) (model r) (representative c) r
        (representative_primitive c) hp (FamilyCurveHeight.modelChange c.m) 1
        (representative_model_change c) (one_smul _ _)).mpr ⟨C,hC⟩
    exact ⟨c,hS,hr,hH⟩

theorem curveSet_good (S : Set CPoint) (H : ℕ)
    (hS : ∀c∈S,GoodCurve (X c.m)) : ∀r∈curveSet S H,GoodCurve (model r) := by
  rintro _ ⟨c,⟨_,hc⟩,rfl⟩
  exact representative_good c (hS c hc)

theorem curveSet_desired (S : Set CPoint) (H : ℕ)
    (hS : ∀c∈S,DesiredCurve (X c.m)) : ∀r∈curveSet S H,DesiredCurve (model r) := by
  intro r hr
  obtain ⟨_,_,c,hc,C,hC⟩ := (mem_curveSet_iff_model S H r).mp hr
  exact desiredCurve_of_change _ _ C hC (hS c hc)

/-- The pre-existing j-image is exactly the fixed j-map applied to the
bounded-height curve-representative set. -/
theorem j_image_factorization (S : Set CPoint) (H : ℕ) :
    FirstHeightRemark.jImageSet S H=j '' curveSet S H := by
  ext z
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨representative c,⟨c,hc,rfl⟩,(j_factorization c).symm⟩
  · rintro ⟨_,⟨c,hc,rfl⟩,rfl⟩
    exact ⟨c,hc,j_factorization c⟩

theorem count_bounds (S : Set CPoint) (H : ℕ) (hFinite : (heightSet H∩S).Finite)
    (hSmooth : ∀c∈S,GoodCurve (X c.m)) :
    FirstHeightRemark.jCount S H≤curveCount S H ∧
      curveCount S H≤(heightSet H∩S).ncard ∧
      (heightSet H∩S).ncard≤192*curveCount S H := by
  refine ⟨?_,Set.ncard_image_le hFinite,?_⟩
  · rw [FirstHeightRemark.jCount,j_image_factorization]
    exact Set.ncard_image_le (hFinite.image representative)
  · exact ncard_le_mul_ncard_refined_image _ hFinite representative
      (fun c => jValue (X c.m)) j j_factorization 192
      (ncard_CPoint_le_192_mul_jimage _ hFinite (fun c hc => hSmooth c hc.2))

theorem ncard_le_192_mul_curve_image (S : Set CPoint) (hS : S.Finite)
    (hSmooth : ∀c∈S,GoodCurve (X c.m)) :
    S.ncard≤192*(representative '' S).ncard :=
  ncard_le_mul_ncard_refined_image S hS representative (fun c => jValue (X c.m)) j
    j_factorization 192 (ncard_CPoint_le_192_mul_jimage S hS hSmooth)

theorem counting_on_cofinite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) (S : Set CPoint)
    (hExceptional : Sᶜ.Finite) (hSmooth : ∀c∈S,GoodCurve (X c.m)) :
    (∀H,(curveSet S H).Finite) ∧ HasLogarithmicCountingExponent (curveCount S) (1/2) := by
  obtain ⟨hFinite,hCount⟩ := FirstCurveHeightCounting.counting hN hMW hDescent hOdd
  obtain ⟨hRestricted,hRestrictedCount⟩ := BoundedHeightCounting.counting_on_cofinite_set
    hFinite hCount (by norm_num) hExceptional
  refine ⟨fun H => (hRestricted H).image _,?_⟩
  apply hRestrictedCount.of_eventually_mul_sandwich (C:=192) (by norm_num) (by decide)
  apply Filter.Eventually.of_forall
  intro H
  exact ⟨Set.ncard_image_le (hRestricted H),
    ncard_le_192_mul_curve_image _ (hRestricted H) (fun c hc => hSmooth c hc.2)⟩

/-- The printed first-family curve count: distinct primitive short
equations of height at most H, with exponent 1/2. -/
theorem remark_6_3_first_family (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hOdd : OddPrimeTorsionIntegrality) :
    (∀H,(curveSet goodParameters H).Finite) ∧
      HasLogarithmicCountingExponent (curveCount goodParameters) (1/2) :=
  counting_on_cofinite hN hMW hDescent hOdd goodParameters
    goodParameters_compl_finite (fun _ hc => hc)

end
end Z2Z4Rank6.FirstCurveRepresentativeCounting
