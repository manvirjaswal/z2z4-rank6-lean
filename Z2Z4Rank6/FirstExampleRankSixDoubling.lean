module

public import Z2Z4Rank6.RankModTwo

@[expose] public section

/-! A generic lower bound for the quotient by doubling at a known rank.
This uses finite generation and full two-torsion. -/
namespace Z2Z4Rank6.RankModTwo
open scoped DirectSum
noncomputable section

/-- Full two-torsion and integral rank r force at least 2^(r+2)doubling classes. -/
theorem card_doubling_lower_of_rank_eq (G : Type) [AddCommGroup G] [AddGroup.FG G]
    (j : ZMod 2×ZMod 2→+G) (hj : Function.Injective j) (r : ℕ)
    (hrank : Module.rank ℤ G=r) : 2^(r+2)≤Nat.card (DoublingQuotient G) := by
  classical
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod G
  let := hι
  have : ∀i : ι,NeZero (p i^e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁i : ι,ZMod (p i^e i)
  have : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hn : n=r := by
    have h := rank_eq_of_free_finite G T f
    rw [hrank] at h
    exact_mod_cast h.symm
  have hfour := four_le_card_finite_double G T f j hj
  have hlower := card_doubling_lower G T f
  calc
    2^(r+2)=2^n*4 := by rw [hn,pow_add]; norm_num
    _ ≤ 2^n*Nat.card (DoublingQuotient T) := Nat.mul_le_mul_left _ hfour
    _ ≤ Nat.card (DoublingQuotient G) := hlower

end
end Z2Z4Rank6.RankModTwo
