module

public import Z2Z4Rank6.ECDescentImage
public import Z2Z4Rank6.MordellWeil
public import Z2Z4Rank6.RankModTwo

@[expose] public section

/-!
# Exact ordinary Mordell--Weil rank of E_C

The doubling quotient has at most 8 classes, by the complete two-descent
certificate, and full rational two-torsion contributes 4 classes.
Finite generation therefore bounds the ordinary integral rank by 1; the
printed point of infinite order supplies the lower bound.
Source: Jaswal, Lemma 4.1(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6

/-- The elementary inclusion (a,b)↦(a,2b) in Z/2×Z/4. -/
def twoTwoToTwoFour : (ZMod 2 × ZMod 2) →+ (ZMod 2 × ZMod 4) where
  toFun x := (x.1,2*(x.2.val : ZMod 4))
  map_zero' := by decide +kernel
  map_add' := by decide +kernel

theorem twoTwoToTwoFour_injective : Function.Injective twoTwoToTwoFour := by
  decide +kernel

/-- Full rational two-torsion, obtained from the explicit split roots. -/
theorem ec_fullTwoTorsion_inclusion :
    ∃ j : (ZMod 2 × ZMod 2) →+ RationalPoints EC, Function.Injective j := by
  obtain ⟨f,hf⟩ := E_two_four_inclusion 27 22 (by norm_num)
  refine ⟨ecSplitEquiv.symm.toAddMonoidHom.comp (f.comp twoTwoToTwoFour),?_⟩
  exact ecSplitEquiv.symm.injective.comp (hf.comp twoTwoToTwoFour_injective)

theorem ec_rank_at_most_one (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints EC) ≤ 1 := by
  let : AddGroup.FG (RationalPoints EC) := hMW EC inferInstance
  obtain ⟨κ,_,hker,_,hcard⟩ := ec_descent_image_bound hDescent
  obtain ⟨j,hj⟩ := ec_fullTwoTorsion_inclusion
  apply RankModTwo.rank_le_of_descent_image_card κ hker j hj 1
  simpa only [show (2 : ℕ)^(1+2)=8 by decide] using hcard

theorem ec_rank_eq_one (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) (hSilvermanVII34 : OddPrimeTorsionIntegrality) :
    Module.rank ℤ (RationalPoints EC) = 1 :=
  le_antisymm (ec_rank_at_most_one hMW hDescent) (ec_rank_at_least_one hSilvermanVII34)

end Z2Z4Rank6
