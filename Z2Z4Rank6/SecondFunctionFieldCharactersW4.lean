import Z2Z4Rank6.SecondFunctionFieldCharactersEmbeddings
import Z2Z4Rank6.SecondFunctionFieldCharacters
import Z2Z4Rank6.SecondW4Reciprocal

/-! The printed W=4 and reciprocal specializations supply the four
character-block independence assertions for the generic sections. -/

namespace Z2Z4Rank6.SecondFunctionField
namespace CharactersBase
noncomputable section
open Polynomial SecondFamily Common.WeierstrassCoordinates SecondFunctionFieldLocal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem singleton_independent {G : Type*} [AddCommGroup G]
    (P : G) (hP : ¬IsOfFinAddOrder P) : LinearIndependent ℤ ![P] := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn i
  have hh : n 0 • P=0 := by simpa [Fin.sum_univ_succ] using hn
  have hzero := (injective_zsmul_iff_not_isOfFinAddOrder.mpr hP)
    (hh.trans (zero_zsmul P).symm)
  fin_cases i
  exact hzero

private theorem independent_of_map {ι G H : Type*} [Fintype ι]
    [AddCommGroup G] [AddCommGroup H] (P : ι → G) (Q : ι → H)
    (f : G →+ H) (hQ : LinearIndependent ℤ Q) (h : ∀ i,f (P i)=Q i) :
    LinearIndependent ℤ P := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp hQ n
  have he := congrArg f hn
  simpa only [map_sum,map_zsmul,map_zero,h] using he

private theorem independent_map {ι G H : Type*} [Fintype ι]
    [AddCommGroup G] [AddCommGroup H] (P : ι → G) (Q : ι → H)
    (f : G →+ H) (hP : LinearIndependent ℤ P) (hinj : Function.Injective f)
    (h : ∀ i,f (P i)=Q i) : LinearIndependent ℤ Q := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  apply Fintype.linearIndependent_iff.mp hP n
  apply hinj
  rw [map_sum,map_zero]
  simpa only [map_zsmul,h] using hn

private theorem independent_pair_map {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (P Q : G) (R S : H) (f : G →+ H) (hPQ : LinearIndependent ℤ ![P,Q])
    (hinj : Function.Injective f) (hPR : f P=R) (hQS : f Q=S) :
    LinearIndependent ℤ ![R,S] := by
  apply independent_map _ _ f hPQ hinj
  intro i
  fin_cases i
  · exact hPR
  · exact hQS

theorem eval_xNumerator (j : Fin 6) (r : ℚ) (hr : r ≠ 0) :
    (xNumerator j).eval r=![x1 r,x2 r,x3 r,x4 r,x5 r,x6 r] j := by
  simpa [Polynomial.aeval_def] using xNumerator_eval r hr j

theorem eval_yNumerator (j : Fin 6) (r : ℚ) (hr : r ≠ 0) :
    (yNumerator j).eval r=![y1 r,y2 r,y3 r,y4 r,y5 r,y6 r] j := by
  simpa [Polynomial.aeval_def] using yNumerator_eval r hr j

theorem exists_W4_specializations (hFormal : FormalGoodReductionHomomorphisms) :
    (∃ f : (curve 0).toAffine.Point →+ (F (4 : ℚ)).toAffine.Point,
      f (point 0)=Q1 (4 : ℚ)) ∧
    (∃ f : (curve 1).toAffine.Point →+ (twistedF (4 : ℚ) (qA 4)).toAffine.Point,
      f (point 1)=Q2twist (4 : ℚ) ∧ f (point 2)=Q3twist (4 : ℚ)) ∧
    (∃ f : (curve 5).toAffine.Point →+ (twistedF (4 : ℚ) (qH 4)).toAffine.Point,
      f (point 5)=Q6twist (4 : ℚ)) := by
  let : (twistedF (4 : ℚ) (twistFactor 4 0)).IsElliptic := SecondW4.fiber_elliptic
  let : (twistedF (4 : ℚ) (twistFactor 4 1)).IsElliptic := SecondW4.qA_fiber_elliptic
  let : (twistedF (4 : ℚ) (twistFactor 4 5)).IsElliptic := SecondW4.qH_fiber_elliptic
  obtain ⟨f0,h0⟩ := exists_specialization hFormal 0 4
  obtain ⟨fA,hA⟩ := exists_specialization hFormal 1 4
  obtain ⟨fH,hH⟩ := exists_specialization hFormal 5 4
  change (curve 0).toAffine.Point →+ (F (4 : ℚ)).toAffine.Point at f0
  change (curve 1).toAffine.Point →+ (twistedF (4 : ℚ) (qA 4)).toAffine.Point at fA
  change (curve 5).toAffine.Point →+ (twistedF (4 : ℚ) (qH 4)).toAffine.Point at fH
  refine ⟨⟨f0,?_⟩,⟨fA,?_,?_⟩,⟨fH,?_⟩⟩
  · apply encode_injective (F (4 : ℚ))
    apply (h0 _ _ _ (encode_point 0)).trans
    rw [eval_xNumerator 0 4 (by norm_num),eval_yNumerator 0 4 (by norm_num)]
    rfl
  · apply encode_injective (twistedF (4 : ℚ) (qA 4))
    apply (hA _ _ _ (encode_point 1)).trans
    rw [eval_xNumerator 1 4 (by norm_num),eval_yNumerator 1 4 (by norm_num)]
    rfl
  · apply encode_injective (twistedF (4 : ℚ) (qA 4))
    apply (hA _ _ _ (encode_point 2)).trans
    rw [eval_xNumerator 2 4 (by norm_num),eval_yNumerator 2 4 (by norm_num)]
    rfl
  · apply encode_injective (twistedF (4 : ℚ) (qH 4))
    apply (hH _ _ _ (encode_point 5)).trans
    rw [eval_xNumerator 5 4 (by norm_num),eval_yNumerator 5 4 (by norm_num)]
    rfl

theorem exists_reciprocal_specialization (hFormal : FormalGoodReductionHomomorphisms) :
    ∃ f : (curve 3).toAffine.Point →+
        (twistedF SecondW4.reciprocalParameter
          (SecondW4.reciprocalParameter*qB SecondW4.reciprocalParameter)).toAffine.Point,
      f (point 3)=Q4twist SecondW4.reciprocalParameter SecondW4.reciprocal_ne_zero ∧
      f (point 4)=Q5twist SecondW4.reciprocalParameter SecondW4.reciprocal_ne_zero := by
  let : (twistedF SecondW4.reciprocalParameter
      (twistFactor SecondW4.reciprocalParameter 3)).IsElliptic := SecondW4.reciprocal_fiber_elliptic
  obtain ⟨f,hf⟩ := exists_specialization hFormal 3 SecondW4.reciprocalParameter
  change (curve 3).toAffine.Point →+
    (twistedF SecondW4.reciprocalParameter
      (SecondW4.reciprocalParameter*qB SecondW4.reciprocalParameter)).toAffine.Point at f
  refine ⟨f,?_,?_⟩
  · apply encode_injective
    apply (hf _ _ _ (encode_point 3)).trans
    rw [eval_xNumerator 3 _ SecondW4.reciprocal_ne_zero,
      eval_yNumerator 3 _ SecondW4.reciprocal_ne_zero]
    rfl
  · apply encode_injective
    apply (hf _ _ _ (encode_point 4)).trans
    rw [eval_xNumerator 4 _ SecondW4.reciprocal_ne_zero,
      eval_yNumerator 4 _ SecondW4.reciprocal_ne_zero]
    rfl

theorem base_blocks_independent
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ ![point 0] ∧
      LinearIndependent ℤ ![point 1,point 2] ∧
      LinearIndependent ℤ ![point 3,point 4] ∧
      LinearIndependent ℤ ![point 5] := by
  obtain ⟨⟨f0,h0⟩,⟨fA,hA1,hA2⟩,⟨fH,hH⟩⟩ := exists_W4_specializations hFormal
  obtain ⟨fB,hB1,hB2⟩ := exists_reciprocal_specialization hFormal
  refine ⟨?_,?_,?_,?_⟩
  · apply independent_of_map _ ![Q1 (4 : ℚ)] f0
      (singleton_independent _ (SecondW4.q1_infinite_order hOdd))
    intro i
    fin_cases i
    exact h0
  · apply independent_of_map _ SecondW4.qAPoints fA
      (SecondW4.qA_points_independent hOdd hReduction hDescent)
    intro i
    fin_cases i
    · exact hA1
    · exact hA2
  · apply independent_of_map _ _ fB
      (SecondW4.reciprocal_points_independent hOdd hReduction hDescent)
    intro i
    fin_cases i
    · exact hB1
    · exact hB2
  · apply independent_of_map _ ![Q6twist (4 : ℚ)] fH
      (singleton_independent _ (SecondW4.q6_infinite_order hOdd))
    intro i
    fin_cases i
    exact hH

theorem embedded_blocks_independent
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ ![points 0] ∧
      LinearIndependent ℤ ![points 1,points 2] ∧
      LinearIndependent ℤ ![points 3,points 4] ∧
      LinearIndependent ℤ ![points 5] := by
  obtain ⟨h0,hA,hB,hH⟩ := base_blocks_independent hOdd hReduction hDescent hFormal
  have hAeq : embed 1=embed 2 :=
    FieldTwistEmbedding.Data.hom_unique (embeddingData 1) (embeddingData 2)
  have hBeq : embed 3=embed 4 :=
    FieldTwistEmbedding.Data.hom_unique (embeddingData 3) (embeddingData 4)
  have hA2 : embed 1 (point 2)=points 2 := by
    rw [hAeq]
    exact embed_point 2
  have hB2 : embed 3 (point 4)=points 4 := by
    rw [hBeq]
    exact embed_point 4
  refine ⟨?_,?_,?_,?_⟩
  · apply independent_map _ _ (embed 0) h0 (embed_injective 0)
    intro i
    fin_cases i
    exact embed_point 0
  · exact independent_pair_map (point 1) (point 2) (points 1) (points 2)
      (embed 1) hA (embed_injective 1) (embed_point 1) hA2
  · exact independent_pair_map (point 3) (point 4) (points 3) (points 4)
      (embed 3) hB (embed_injective 3) (embed_point 3) hB2
  · apply independent_map _ _ (embed 5) hH (embed_injective 5)
    intro i
    fin_cases i
    exact embed_point 5

end
end CharactersBase

noncomputable section
theorem points_independent_via_W4_characters
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points := by
  obtain ⟨h0,hA,hB,hH⟩ := CharactersBase.embedded_blocks_independent hOdd hReduction hDescent hFormal
  exact points_independent_of_blocks h0 hA hB hH

/-- Theorem 8.1(b), using the printed W=4 arithmetic, the reciprocal
involution, untwisting, and the four distinct character spaces. -/
theorem theorem_8_1_b_via_W4
    (hOdd : OddPrimeTorsionIntegrality) (hReduction : GoodReductionHomomorphisms)
    (hDescent : CompleteTwoDescentTheorem) (hFormal : FormalGoodReductionHomomorphisms) :
    LinearIndependent ℤ points ∧ 6≤Module.rank ℤ (SecondFamily.F W).toAffine.Point := by
  have h := points_independent_via_W4_characters hOdd hReduction hDescent hFormal
  exact ⟨h,by simpa using h.cardinal_le_rank⟩

end
end Z2Z4Rank6.SecondFunctionField
