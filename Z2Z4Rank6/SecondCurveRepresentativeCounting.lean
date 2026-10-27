import Z2Z4Rank6.PrimitiveCurveRepresentatives
import Z2Z4Rank6.SecondHeightRemark

/-!
# Distinct primitive-short second-family curves at bounded curve height

Jaswal, Remark 6.3, DOI 10.5281/zenodo.23437117. The normalized
primitive integer pairs represent the rational isomorphism classes of
smooth family fibers. Their coefficient height is bounded by H;
the count has logarithmic exponent 1. Its map to j-values is fixed,
and every smooth representative fiber has at most 96 base points.
-/
namespace Z2Z4Rank6.SecondCurveRepresentativeCounting
open WeierstrassCurve SecondFamily SecondCurveHeightCounting
open PrimitiveCurveRepresentatives
noncomputable section

def representative (P : G2Point ℚ) : Coefficients :=
  ((SecondFamilyCurveHeight.normalization P.W).shortA,(SecondFamilyCurveHeight.normalization P.W).shortB)

theorem representative_primitive (P : G2Point ℚ) :
    ShortHeight.ShortPrimitive (representative P).1 (representative P).2 :=
  SecondFamilyCurveHeight.normalized_primitive P.W

theorem representative_model_change (P : G2Point ℚ) :
    SecondFamilyCurveHeight.modelChange P.W • F P.W=model (representative P) :=
  SecondFamilyCurveHeight.modelChange_eq P.W

theorem representative_eq_iff (P Q : G2Point ℚ) :
    representative P=representative Q ↔ ∃C : VariableChange ℚ,C • F P.W=F Q.W :=
  coefficients_eq_iff_exists_change _ _ _ _ (representative_primitive P)
    (representative_primitive Q) _ _ (representative_model_change P) (representative_model_change Q)

theorem j_factorization (P : G2Point ℚ) : jValue (F P.W)=j (representative P) :=
  PrimitiveCurveRepresentatives.j_factorization _ _ _ (representative_model_change P)

theorem height_factorization (P : G2Point ℚ) :
    PrimitiveCurveRepresentatives.height (representative P)=curveHeight P := rfl

theorem representative_good (P : G2Point ℚ) (hP : GoodCurve (F P.W)) :
    GoodCurve (model (representative P)) := by
  let := hP
  exact SecondFamilyCurveHeight.normalizedModel_isElliptic P.W

theorem finite_representative_fiber (r : Coefficients) :
    {P : G2Point ℚ | GoodCurve (F P.W) ∧ representative P=r}.Finite := by
  apply (finite_j_G2Point_fiber (j r)).subset
  rintro P ⟨hP,hr⟩
  exact ⟨hP,(j_factorization P).trans (congrArg j hr)⟩

theorem ncard_representative_fiber_le (r : Coefficients) :
    {P : G2Point ℚ | GoodCurve (F P.W) ∧ representative P=r}.ncard≤96 :=
  (Set.ncard_le_ncard (fun P hP =>
    ⟨hP.1,(j_factorization P).trans (congrArg j hP.2)⟩ :
      {P : G2Point ℚ | GoodCurve (F P.W) ∧ representative P=r}⊆
        {P : G2Point ℚ | GoodCurve (F P.W) ∧ jValue (F P.W)=j r})
    (finite_j_G2Point_fiber (j r))).trans (ncard_j_G2Point_fiber_le (j r))

def curveSet (S : Set (G2Point ℚ)) (H : ℕ) : Set Coefficients :=
  representative '' (heightSet H∩S)
def curveCount (S : Set (G2Point ℚ)) (H : ℕ) : ℕ := (curveSet S H).ncard

theorem mem_curveSet_iff (S : Set (G2Point ℚ)) (H : ℕ) (r : Coefficients) :
    r∈curveSet S H ↔ ∃P∈S,representative P=r ∧ PrimitiveCurveRepresentatives.height r≤H := by
  constructor
  · rintro ⟨P,⟨hP,hS⟩,rfl⟩
    exact ⟨P,hS,rfl,hP⟩
  · rintro ⟨P,hS,hr,hH⟩
    refine ⟨P,⟨?_,hS⟩,hr⟩
    rw [←hr] at hH
    exact hH

/-- Exact primitive-short interpretation, with the rational change
and coefficient-height bound present in the membership statement. -/
theorem mem_curveSet_iff_model (S : Set (G2Point ℚ)) (H : ℕ) (r : Coefficients) :
    r∈curveSet S H ↔ ShortHeight.ShortPrimitive r.1 r.2 ∧
      PrimitiveCurveRepresentatives.height r≤H ∧
      ∃P∈S,∃C : VariableChange ℚ,C • F P.W=model r := by
  rw [mem_curveSet_iff]
  constructor
  · rintro ⟨P,hS,rfl,hH⟩
    exact ⟨representative_primitive P,hH,P,hS,_,representative_model_change P⟩
  · rintro ⟨hp,hH,P,hS,C,hC⟩
    have hr : representative P=r :=
      (coefficients_eq_iff_exists_change (F P.W) (model r) (representative P) r
        (representative_primitive P) hp (SecondFamilyCurveHeight.modelChange P.W) 1
        (representative_model_change P) (one_smul _ _)).mpr ⟨C,hC⟩
    exact ⟨P,hS,hr,hH⟩

theorem curveSet_good (S : Set (G2Point ℚ)) (H : ℕ)
    (hS : ∀P∈S,GoodCurve (F P.W)) : ∀r∈curveSet S H,GoodCurve (model r) := by
  rintro _ ⟨P,⟨_,hP⟩,rfl⟩
  exact representative_good P (hS P hP)

theorem curveSet_desired (S : Set (G2Point ℚ)) (H : ℕ)
    (hS : ∀P∈S,DesiredCurve (F P.W)) : ∀r∈curveSet S H,DesiredCurve (model r) := by
  intro r hr
  obtain ⟨_,_,P,hP,C,hC⟩ := (mem_curveSet_iff_model S H r).mp hr
  exact desiredCurve_of_change _ _ C hC (hS P hP)

theorem j_image_factorization (S : Set (G2Point ℚ)) (H : ℕ) :
    SecondHeightRemark.jImageSet S H=j '' curveSet S H := by
  ext z
  constructor
  · rintro ⟨P,hP,rfl⟩
    exact ⟨representative P,⟨P,hP,rfl⟩,(j_factorization P).symm⟩
  · rintro ⟨_,⟨P,hP,rfl⟩,rfl⟩
    exact ⟨P,hP,j_factorization P⟩

theorem count_bounds (S : Set (G2Point ℚ)) (H : ℕ) (hFinite : (heightSet H∩S).Finite)
    (hSmooth : ∀P∈S,GoodCurve (F P.W)) :
    SecondHeightRemark.jCount S H≤curveCount S H ∧
      curveCount S H≤(heightSet H∩S).ncard ∧
      (heightSet H∩S).ncard≤96*curveCount S H := by
  refine ⟨?_,Set.ncard_image_le hFinite,?_⟩
  · rw [SecondHeightRemark.jCount,j_image_factorization]
    exact Set.ncard_image_le (hFinite.image representative)
  · exact ncard_le_mul_ncard_refined_image _ hFinite representative
      (fun P => jValue (F P.W)) j j_factorization 96
      (ncard_G2Point_le_96_mul_jimage _ hFinite (fun P hP => hSmooth P hP.2))

theorem ncard_le_96_mul_curve_image (S : Set (G2Point ℚ)) (hS : S.Finite)
    (hSmooth : ∀P∈S,GoodCurve (F P.W)) : S.ncard≤96*(representative '' S).ncard :=
  ncard_le_mul_ncard_refined_image S hS representative (fun P => jValue (F P.W)) j
    j_factorization 96 (ncard_G2Point_le_96_mul_jimage S hS hSmooth)

theorem counting_on_cofinite (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) (S : Set (G2Point ℚ))
    (hExceptional : Sᶜ.Finite) (hSmooth : ∀P∈S,GoodCurve (F P.W)) :
    (∀H,(curveSet S H).Finite) ∧ HasLogarithmicCountingExponent (curveCount S) 1 := by
  obtain ⟨hFinite,hCount⟩ := SecondCurveHeightCounting.counting hN hMW hMazur hDescent
  obtain ⟨hRestricted,hRestrictedCount⟩ := BoundedHeightCounting.counting_on_cofinite_set
    hFinite hCount (by norm_num) hExceptional
  refine ⟨fun H => (hRestricted H).image _,?_⟩
  apply hRestrictedCount.of_eventually_mul_sandwich (C:=96) (by norm_num) (by decide)
  apply Filter.Eventually.of_forall
  intro H
  exact ⟨Set.ncard_image_le (hRestricted H),
    ncard_le_96_mul_curve_image _ (hRestricted H) (fun P hP => hSmooth P hP.2)⟩

/-- Distinct primitive-short curves of height at most H have the
second-family exponent 1 asserted in Remark 6.3. -/
theorem remark_6_3_second_family (hN : NeronRigidCountingTheorem.{0})
    (hMW : MordellWeilTheorem) (hMazur : MazurTorsionTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    (∀H,(curveSet goodParameters H).Finite) ∧
      HasLogarithmicCountingExponent (curveCount goodParameters) 1 :=
  counting_on_cofinite hN hMW hMazur hDescent goodParameters
    goodParameters_compl_finite (fun _ hP => hP)

end
end Z2Z4Rank6.SecondCurveRepresentativeCounting
