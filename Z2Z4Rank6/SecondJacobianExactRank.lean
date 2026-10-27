module

public import Z2Z4Rank6.SecondJacobianRankLower
public import Z2Z4Rank6.SecondJacobianSelmerChecks
public import Z2Z4Rank6.SplitDescentImage
public import Z2Z4Rank6.ECExactRank

@[expose] public section

/-!
# The printed second Jacobian has ordinary rank exactly two

The upper bound uses complete descent coordinates and proved local
covering obstructions. The hypotheses are the Mordell--Weil and complete two-descent theorems. The
lower bound uses the two printed independent points.
-/
namespace Z2Z4Rank6

theorem secondJacobian_descent_image_bound
    (κ:RationalPoints J2→+(RatSquareClassAdd×RatSquareClassAdd))
    (hκ:∀P,κ P=completeDescentCoordinates (E 393129 25921) 0
      (-154550410641) (-671898241) (secondJacobianSplitEquiv P)) :
    Finite κ.range ∧ Nat.card κ.range≤16 := by
  have hsub : (κ.range:Set (RatSquareClassAdd×RatSquareClassAdd)) ⊆
      fullTwoSelmerClasses SecondJacobianSelmer.A SecondJacobianSelmer.B := by
    rintro q ⟨P,rfl⟩
    rw [hκ]
    exact split_completeDescent_coordinates_mem (E (393129:ℚ) 25921)
      SecondJacobianSelmer.A SecondJacobianSelmer.B
      (by norm_num [SecondJacobianSelmer.A]) (by norm_num [SecondJacobianSelmer.B])
      (by norm_num [SecondJacobianSelmer.A,SecondJacobianSelmer.B])
      (by convert E_eq_splitWeierstrass (393129:ℚ) 25921 using 1; norm_num [SecondJacobianSelmer.A,SecondJacobianSelmer.B]) _
  refine ⟨(SecondJacobianSelmer.classes_finite.subset hsub).to_subtype,?_⟩
  change (κ.range:Set (RatSquareClassAdd×RatSquareClassAdd)).ncard≤16
  exact (Set.ncard_le_ncard hsub SecondJacobianSelmer.classes_finite).trans
    SecondJacobianSelmer.classes_card_le

theorem secondJacobian_descent_image_bounded (hDescent:CompleteTwoDescentTheorem) :
    ∃κ:RationalPoints J2→+(RatSquareClassAdd×RatSquareClassAdd),
      (∀P,κ P=completeDescentCoordinates (E 393129 25921) 0
        (-154550410641) (-671898241) (secondJacobianSplitEquiv P)) ∧
      (∀P,κ P=0 ↔ ∃Q:RationalPoints J2,(2:ℕ)•Q=P) ∧ Nat.card κ.range≤16 := by
  obtain ⟨κ,hκ,hker⟩ := hDescent (E (393129:ℚ) 25921) 0 (-154550410641) (-671898241)
    secondJacobianSplit_isElliptic
    (by convert E_eq_splitWeierstrass (393129:ℚ) 25921 using 1; norm_num)
  let κJ : RationalPoints J2→+(RatSquareClassAdd×RatSquareClassAdd) :=
    κ.comp secondJacobianSplitEquiv.toAddMonoidHom
  have hval : ∀P,κJ P=completeDescentCoordinates (E 393129 25921) 0
      (-154550410641) (-671898241) (secondJacobianSplitEquiv P) := fun P=>hκ _
  refine ⟨κJ,hval,?_,(secondJacobian_descent_image_bound κJ hval).2⟩
  intro P
  change κ (secondJacobianSplitEquiv P)=0 ↔ _
  rw [hker]
  constructor
  · rintro ⟨Q,hQ⟩
    refine ⟨secondJacobianSplitEquiv.symm Q,secondJacobianSplitEquiv.injective ?_⟩
    simpa only [map_nsmul,AddEquiv.apply_symm_apply] using hQ
  · rintro ⟨Q,rfl⟩
    exact ⟨secondJacobianSplitEquiv Q,(map_nsmul secondJacobianSplitEquiv 2 Q).symm⟩

theorem secondJacobian_fullTwoTorsion_inclusion :
    ∃j:(ZMod 2×ZMod 2)→+RationalPoints J2,Function.Injective j := by
  obtain ⟨f,hf⟩ := E_two_four_inclusion 393129 25921 (by norm_num)
  refine ⟨secondJacobianSplitEquiv.symm.toAddMonoidHom.comp (f.comp twoTwoToTwoFour),?_⟩
  exact secondJacobianSplitEquiv.symm.injective.comp (hf.comp twoTwoToTwoFour_injective)

theorem secondJacobian_rank_at_most_two (hMW:MordellWeilTheorem)
    (hDescent:CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints J2)≤2 := by
  let : AddGroup.FG (RationalPoints J2) := hMW J2 inferInstance
  obtain ⟨κ,_,hker,hcard⟩ := secondJacobian_descent_image_bounded hDescent
  obtain ⟨j,hj⟩ := secondJacobian_fullTwoTorsion_inclusion
  apply RankModTwo.rank_le_of_descent_image_card κ hker j hj 2
  exact hcard

theorem secondJacobian_rank_eq_two (hMW:MordellWeilTheorem) (hMazur:MazurTorsionTheorem)
    (hDescent:CompleteTwoDescentTheorem) : Module.rank ℤ (RationalPoints J2)=2 :=
  le_antisymm (secondJacobian_rank_at_most_two hMW hDescent)
    (secondJacobian_rank_at_least_two hMazur hDescent)

/-- The four already checked original-root descent values force sixteen
classes in every homomorphism with those coordinate values. -/
theorem secondJacobian_descent_image_card_lower
    (κ:RationalPoints J2→+(RatSquareClassAdd×RatSquareClassAdd)) [Finite κ.range]
    (hκ:∀P,κ P=completeDescentCoordinates J2
      (-102809641014) 51068871386 51740769627 P) : 16≤Nat.card κ.range := by
  classical
  have hv : ∀i,κ (secondJacobianFourPoints i)=secondJacobianBasis i :=
    fun i=>(hκ _).trans (secondJacobian_descent_coordinates i)
  let f : (Fin 4→ZMod 2)→κ.range := fun a=>
    ⟨κ (∑i,(a i).val • secondJacobianFourPoints i),⟨_,rfl⟩⟩
  have hf : ∀a,(f a).val=Fintype.linearCombination (ZMod 2) secondJacobianBasis a := by
    intro a
    change κ (∑i,(a i).val • secondJacobianFourPoints i)=∑i,a i • secondJacobianBasis i
    simp only [map_sum,map_nsmul,hv]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [ZMod.natCast_zmod_val] using
      (Nat.cast_smul_eq_nsmul (ZMod 2) (a i).val (secondJacobianBasis i)).symm
  have hinj : Function.Injective f := by
    intro a b hab
    apply secondJacobian_basis_independent.fintypeLinearCombination_injective
    simpa only [hf] using congrArg Subtype.val hab
  have hc:=Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_eq_fintype_card,ZMod.card] using hc

/-- Both coordinate conventions have the same doubling kernel. -/
theorem secondJacobian_doubling_quotient_card (hDescent:CompleteTwoDescentTheorem) :
    Nat.card (RankModTwo.DoublingQuotient (RationalPoints J2))=16 := by
  obtain ⟨κ,hκ,hker,hupper⟩ := secondJacobian_descent_image_bounded hDescent
  obtain ⟨κ0,hκ0,hker0⟩ := hDescent J2 (-102809641014) 51068871386 51740769627
    secondJacobian_isElliptic secondJacobian_eq_split
  let : Finite κ.range := (secondJacobian_descent_image_bound κ hκ).1
  let : Finite (RankModTwo.DoublingQuotient (RationalPoints J2)) :=
    Finite.of_equiv κ.range (RankModTwo.doublingQuotientEquivRange κ hker).symm.toEquiv
  let : Finite κ0.range := Finite.of_equiv
    (RankModTwo.DoublingQuotient (RationalPoints J2))
    (RankModTwo.doublingQuotientEquivRange κ0 hker0).toEquiv
  apply Nat.le_antisymm
  · rw [RankModTwo.card_doubling_eq_range κ hker]
    exact hupper
  · rw [RankModTwo.card_doubling_eq_range κ0 hker0]
    exact secondJacobian_descent_image_card_lower κ0 hκ0

theorem secondJacobian_descent_image_exact (hDescent:CompleteTwoDescentTheorem) :
    ∃κ:RationalPoints J2→+(RatSquareClassAdd×RatSquareClassAdd),
      (∀P,κ P=completeDescentCoordinates (E 393129 25921) 0
        (-154550410641) (-671898241) (secondJacobianSplitEquiv P)) ∧
      (∀P,κ P=0 ↔ ∃Q:RationalPoints J2,(2:ℕ)•Q=P) ∧ Nat.card κ.range=16 := by
  obtain ⟨κ,hκ,hker,_⟩ := secondJacobian_descent_image_bounded hDescent
  refine ⟨κ,hκ,hker,?_⟩
  rw [←RankModTwo.card_doubling_eq_range κ hker]
  exact secondJacobian_doubling_quotient_card hDescent

end Z2Z4Rank6
