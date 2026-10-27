module

public import Z2Z4Rank6.GFunctionFieldPointPlace
public import Z2Z4Rank6.GFunctionFieldSpecialization
public import Z2Z4Rank6.SilvermanRigidSpecialization
public import Z2Z4Rank6.JTranscendence
public import Z2Z4Rank6.SingularFibers
public import Mathlib.Algebra.Module.Rat

@[expose] public section

/-!
# Cofinite rank five on the rational curve G

The quadratic function field Q(G) has transcendental j. Every rational
G-point gives a distinct normalized Laurent place, and only finitely many
lie over singular parameters. Silverman's generic theorem therefore has
finitely many exceptions on the rational G-point set. Its
injective specialization preserves the five proved independent points.
-/
namespace Z2Z4Rank6
noncomputable section
open scoped Classical
open Polynomial CanonicalLaurentSpecialization

local instance gFamilyScalarTower :
    @IsScalarTower ℚ (RatFunc ℚ) GFunctionField.K
      (inferInstance : SMul ℚ (RatFunc ℚ))
      (Algebra.toSMul : SMul (RatFunc ℚ) GFunctionField.K)
      (Algebra.toSMul : SMul ℚ GFunctionField.K) := by
  let : Algebra ℚ (RatFunc ℚ) := RatFunc.instAlgebraOfPolynomial ℚ ℚ
  exact IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=RatFunc ℚ) (A:=GFunctionField.K)
    (Subsingleton.elim _ _)

namespace GFunctionField

/-- Polynomial evaluation through the rational function field. -/
theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base K (algebraMap ℚ[X] Base p)=aeval m p := by
  have hC : (algebraMap Base K).comp (RatFunc.C : ℚ →+* Base)=algebraMap ℚ K :=
    Subsingleton.elim _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n r =>
    have hr := RingHom.congr_fun hC r
    simp only [RingHom.comp_apply] at hr
    simp only [RatFunc.algebraMap_monomial,map_mul,map_pow,aeval_monomial,m,hr]

private theorem embedded_numerator :
    algebraMap Base K (algebraMap ℚ[X] Base jNumerator)=
      256*((a m)^4-(a m)^2*(b m)^2+(b m)^4)^3 := by
  rw [polynomial_embedding]
  simp [jNumerator,a,b,map_ofNat]

private theorem embedded_denominator :
    algebraMap Base K (algebraMap ℚ[X] Base jDenominator)=
      (a m)^4*(b m)^4*((a m)^2-(b m)^2)^2 := by
  rw [polynomial_embedding]
  simp [jDenominator,a,b,map_ofNat]

/-- The generic invariant equals the embedded checked rational function. -/
theorem j_eq_base_embedding : (X m).j=algebraMap Base K jRationalFunction := by
  rw [jRationalFunction,map_div₀]
  apply j_eq_of_scaled_invariant_parts _ _ _ 16 (by norm_num)
  · rw [embedded_numerator]
    simp only [X,E,WeierstrassCurve.c₄,WeierstrassCurve.b₂,WeierstrassCurve.b₄]
    ring
  · rw [embedded_denominator]
    simp only [X,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring

/-- Mathlib's generic j-invariant over Q(G) is transcendental. -/
theorem j_transcendental : Transcendental ℚ (X m).j := by
  rw [j_eq_base_embedding]
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  exact jRationalFunction_transcendental

end GFunctionField

namespace GCofiniteRank
open GFunctionFieldPointPlace

/-- Five integer-linearly independent rational points. -/
def RankAtLeastFive (W : WeierstrassCurve ℚ) : Prop :=
  ∃ P : Fin 5 → RationalPoints W, LinearIndependent ℤ P

/-- The ordinary additive rank of the rational point group is at least 5. -/
def ordinaryRankAtLeastFive (W : WeierstrassCurve ℚ) : Prop :=
  5≤Module.rank ℤ (RationalPoints W)

theorem ordinaryRank_of_independent (W : WeierstrassCurve ℚ) (h : RankAtLeastFive W) :
    ordinaryRankAtLeastFive W := by
  obtain ⟨P,hP⟩ := h
  simpa [ordinaryRankAtLeastFive] using hP.cardinal_le_rank

def GoodParameters := {c : GQuarticPoint // ¬singularParameter c.m}

/-- The normalized good place at a rational point of G. -/
def actualPlace (c : GoodParameters) : RigidGoodPlace GFunctionField.K (X GFunctionField.m) where
  parameter := c.val.m
  embedding := embeddingAlgHom c.val
  rigid := embeddingAlgHom_parameter c.val
  model := seriesCurve c.val
  model_eq := seriesCurve_laurent c.val
  good := constantFiber_elliptic c.val ((X_good_iff_not_singular_parameter c.val.m).mpr c.property)

theorem actualPlace_injective : Function.Injective actualPlace := by
  intro c d h
  apply Subtype.ext
  apply embeddingAlgHom_injective_on_points
  exact congrArg RigidGoodPlace.embedding h

/-- Injective specialization preserves the five independent sections. -/
theorem rankAtLeastFive_of_place_specialization
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) (c : GoodParameters)
    (hc : RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace c)) :
    RankAtLeastFive (X c.val.m) := by
  obtain ⟨σ,hσ,_⟩ := hc
  let τ : (X GFunctionField.m).toAffine.Point →+ (X c.val.m).toAffine.Point :=
    (pointEquivOfEq (seriesCurve_constant c.val)).toAddMonoidHom.comp σ
  have hτ : Function.Injective τ :=
    (pointEquivOfEq (seriesCurve_constant c.val)).injective.comp hσ
  refine ⟨fun i=>τ (GFunctionField.points i),Fintype.linearIndependent_iff.mpr ?_⟩
  intro a ha
  apply Fintype.linearIndependent_iff.mp
    (GFunctionField.points_independent hMazur hReduction hFormal) a
  apply hτ
  simpa only [map_sum,map_zsmul,map_zero] using ha

/-- Only finitely many rational G-points lie over the nine singular parameters. -/
theorem singularPoints_finite : {c : GQuarticPoint | singularParameter c.m}.Finite := by
  have hm : {r : ℚ | singularParameter r}.Finite := by
    change (({0,1,-1,9,-9,11,-11,99,-99} : Finset ℚ) : Set ℚ).Finite
    exact Finset.finite_toSet _
  exact hm.preimage' (fun r _=>finite_m_fiber r)

/-- The rank-five conclusion fails at only finitely many rational G-points. -/
theorem finite_rank_failures
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    {c : GQuarticPoint | ¬RankAtLeastFive (X c.m)}.Finite := by
  let : FiniteDimensional GFunctionField.Base GFunctionField.K :=
    Module.Finite.of_basis (QuadraticAlgebra.basis GFunctionField.d 0)
  have hbad := finite_bad_rigid_places hSilverman (X GFunctionField.m)
    inferInstance GFunctionField.j_transcendental
  have hpull : (actualPlace ⁻¹' RigidGoodPlace.badPlaces (X GFunctionField.m)).Finite :=
    hbad.preimage actualPlace_injective.injOn
  apply (singularPoints_finite.union (hpull.image Subtype.val)).subset
  intro c hc
  by_cases he : singularParameter c.m
  · exact Or.inl he
  · refine Or.inr ⟨⟨c,he⟩,?_,rfl⟩
    change ¬RigidGoodPlace.HasInjectiveCanonicalSpecialization (actualPlace ⟨c,he⟩)
    intro hspec
    exact hc (rankAtLeastFive_of_place_specialization hMazur hReduction hFormal ⟨c,he⟩ hspec)

theorem finite_ordinary_rank_failures
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    {c : GQuarticPoint | ¬ordinaryRankAtLeastFive (X c.m)}.Finite := by
  apply (finite_rank_failures hSilverman hMazur hReduction hFormal).subset
  intro c hc hr
  exact hc (ordinaryRank_of_independent (X c.m) hr)

theorem ordinary_rank_cofinite
    (hSilverman : SilvermanRigidSpecializationTheorem.{0})
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms) :
    ∀ᶠ c : GQuarticPoint in Filter.cofinite, ordinaryRankAtLeastFive (X c.m) :=
  Filter.eventually_cofinite.mpr
    (finite_ordinary_rank_failures hSilverman hMazur hReduction hFormal)

/-- Every fixed rational j-value occurs at finitely many smooth G-fibers. -/
theorem finite_j_GQuarticPoint_fiber (j : ℚ) :
    {c : GQuarticPoint | GoodCurve (X c.m) ∧ jValue (X c.m)=j}.Finite := by
  have hf := (finite_j_parameter_roots j).preimage' (fun r _=>finite_m_fiber r)
  apply hf.subset
  intro c hc
  change (jNumerator-Polynomial.C j*jDenominator).eval c.m=0
  simp only [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  have he : jNumerator.eval c.m/jDenominator.eval c.m=j :=
    (jValue_X_eq c.m hc.1).symm.trans hc.2
  exact sub_eq_zero.mpr ((div_eq_iff (jDenominator_ne_zero c.m hc.1)).mp he)

end GCofiniteRank
end
end Z2Z4Rank6
