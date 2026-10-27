module

public import Z2Z4Rank6.TwistCharacterRanks
public import Z2Z4Rank6.GusicTadicModels
public import Z2Z4Rank6.FirstFunctionFieldStatements
public import Z2Z4Rank6.FunctionFieldFiniteGeneration

@[expose] public section

/-!
# Assembly of the four twist ranks

The algebraic assembly for Theorem 1.2(b) and Proposition 5.2 of Jaswal,
DOI 10.5281/zenodo.23437117. The finite descent certificates are separate.
-/

namespace Z2Z4Rank6.RankSixAssembly

noncomputable section
open FunctionField FunctionField.TwistCharacters

def fourProductEquiv {R : Type*} [CommSemiring R]
    (M : Bool × Bool → Type*) [∀ χ, AddCommMonoid (M χ)] [∀ χ, Module R (M χ)] :
    (∀ χ, M χ) ≃ₗ[R] M (false,false) × M (true,false) × M (false,true) × M (true,true) where
  toFun f := (f (false,false),f (true,false),f (false,true),f (true,true))
  invFun x χ := match χ with
    | (false,false) => x.1
    | (true,false) => x.2.1
    | (false,true) => x.2.2.1
    | (true,true) => x.2.2.2
  left_inv f := by funext ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv x := by rcases x with ⟨a,b,c,d⟩; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_four_twists : Module.rank ℤ PointGroup =
    Module.rank ℤ (twistPoints (false,false)) + Module.rank ℤ (twistPoints (true,false)) +
    Module.rank ℤ (twistPoints (false,true)) + Module.rank ℤ (twistPoints (true,true)) := by
  rw [pointGroup_rank_eq_rationalized_rank]
  have e := characterDecomposition.trans (fourProductEquiv (R:=ℚ) (fun χ => ↥(characterSpace χ)))
  rw [e.rank_eq]
  simp only [rank_prod',←twist_rank_eq_character_rank]
  ac_rfl

theorem twistCurve_q1_model : twistCurve (true,false)=GusicTadic.genericModel GusicTadic.q1Poly := by
  rw [twistCurve_q1]
  ext <;> simp [paperTwist,PointScaling.curve,A,B,GusicTadic.genericModel,
    GusicTadic.twistModel,GusicTadic.polyToRF,GusicTadic.q1Poly,q1,map_ofNat]; ring

theorem twistCurve_q2_model : twistCurve (false,true)=GusicTadic.genericModel GusicTadic.q2Poly := by
  rw [twistCurve_q2]
  ext <;> simp [paperTwist,PointScaling.curve,A,B,GusicTadic.genericModel,
    GusicTadic.twistModel,GusicTadic.polyToRF,GusicTadic.q2Poly,q2,map_ofNat]; ring

theorem twistCurve_q12_model : twistCurve (true,true)=GusicTadic.genericModel GusicTadic.q12Poly := by
  rw [twistCurve_q12]
  ext <;> simp [paperTwist,PointScaling.curve,A,B,GusicTadic.genericModel,
    GusicTadic.twistModel,GusicTadic.polyToRF,GusicTadic.q12Poly,q12,map_ofNat]; ring

theorem rank_le_six_of_bounds
    (h0 : Module.rank ℤ (twistPoints (false,false))≤3)
    (h1 : Module.rank ℤ (twistPoints (true,false))≤1)
    (h2 : Module.rank ℤ (twistPoints (false,true))≤1)
    (h3 : Module.rank ℤ (twistPoints (true,true))≤1) :
    Module.rank ℤ PointGroup≤6 := by
  rw [rank_four_twists]
  calc
    _ ≤ (3:Cardinal)+1+1+1 := add_le_add (add_le_add (add_le_add h0 h1) h2) h3
    _=6 := by norm_num

theorem rank_eq_six_of_bounds
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (h0 : Module.rank ℤ (twistPoints (false,false))≤3)
    (h1 : Module.rank ℤ (twistPoints (true,false))≤1)
    (h2 : Module.rank ℤ (twistPoints (false,true))≤1)
    (h3 : Module.rank ℤ (twistPoints (true,true))≤1) :
    Module.rank ℤ PointGroup=6 := by
  apply le_antisymm (rank_le_six_of_bounds h0 h1 h2 h3)
  exact generic_rank_at_least_six hMazur hReduction hFormal

theorem twists_rank_one_of_bounds
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (h0 : Module.rank ℤ (twistPoints (false,false))≤3)
    (h1 : Module.rank ℤ (twistPoints (true,false))≤1)
    (h2 : Module.rank ℤ (twistPoints (false,true))≤1)
    (h3 : Module.rank ℤ (twistPoints (true,true))≤1) :
    Module.rank ℤ (twistPoints (true,false))=1 ∧
    Module.rank ℤ (twistPoints (false,true))=1 ∧
    Module.rank ℤ (twistPoints (true,true))=1 := by
  have h6 := rank_eq_six_of_bounds hMazur hReduction hFormal h0 h1 h2 h3
  rw [rank_four_twists] at h6
  have hne1 : Module.rank ℤ (twistPoints (true,false))≠0 := by
    intro hz
    have hh := add_le_add (add_le_add (add_le_add h0 (le_of_eq hz)) h2) h3
    rw [h6] at hh
    norm_num at hh
  have hne2 : Module.rank ℤ (twistPoints (false,true))≠0 := by
    intro hz
    have hh := add_le_add (add_le_add (add_le_add h0 h1) (le_of_eq hz)) h3
    rw [h6] at hh
    norm_num at hh
  have hne3 : Module.rank ℤ (twistPoints (true,true))≠0 := by
    intro hz
    have hh := add_le_add (add_le_add (add_le_add h0 h1) h2) (le_of_eq hz)
    rw [h6] at hh
    norm_num at hh
  exact ⟨le_antisymm h1 (Cardinal.one_le_iff_ne_zero.mpr hne1),
    le_antisymm h2 (Cardinal.one_le_iff_ne_zero.mpr hne2),
    le_antisymm h3 (Cardinal.one_le_iff_ne_zero.mpr hne3)⟩

theorem finiteIndex_of_bounds
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms)
    (hFormal : FormalGoodReductionHomomorphisms)
    (hMWLN : MordellWeilLangNeronTheorem.{0})
    (h0 : Module.rank ℤ (twistPoints (false,false))≤3)
    (h1 : Module.rank ℤ (twistPoints (true,false))≤1)
    (h2 : Module.rank ℤ (twistPoints (false,true))≤1)
    (h3 : Module.rank ℤ (twistPoints (true,true))≤1) : GenericSixFiniteIndex := by
  let : Module.Finite ℤ GenericPoints := FunctionField.pointGroup_moduleFinite hMWLN
  exact genericSixFiniteIndex_of_rank_and_finite_generation hMazur hReduction hFormal
    (rank_eq_six_of_bounds hMazur hReduction hFormal h0 h1 h2 h3)

end
end Z2Z4Rank6.RankSixAssembly
