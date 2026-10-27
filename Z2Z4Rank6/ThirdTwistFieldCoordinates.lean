module

public import Z2Z4Rank6.ThirdTwistField

@[expose] public section

/-! The displayed coordinates generate the third-twist fields,
and their parameter is transcendental. -/

namespace Z2Z4Rank6.ThirdTwistField
noncomputable section
open Polynomial

theorem generic_polynomial_embedding {L : Type*} [Field L] [Algebra ℚ L]
    (f : Base →+* L) (p : ℚ[X]) :
    f (algebraMap ℚ[X] Base p)=aeval (f RatFunc.X) p := by
  have hc : f.comp (RatFunc.C : ℚ →+* Base)=algebraMap ℚ L := RingHom.ext_rat _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n c =>
    have h := RingHom.congr_fun hc c
    simp only [RingHom.comp_apply] at h
    simp only [RatFunc.algebraMap_monomial,map_mul,map_pow,aeval_monomial,h]

theorem m_transcendental : Transcendental ℚ m := by
  rw [m_eq_base]
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base K (algebraMap ℚ[X] Base p)=aeval m p := by
  rw [m_eq_base]
  exact generic_polynomial_embedding (algebraMap Base K) p

def basis : Module.Basis ((Fin 2 × Fin 2) × Fin 2) Base K :=
  FunctionField.basis.smulTower (QuadraticAlgebra.basis d3Old 0)

theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,u,v,w} : Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,u,v,w} : Set K)
  have hm : m∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hv : v∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hw : w∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hsimple : IntermediateField.adjoin ℚ ({m} : Set K)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hm
  have hbase (r : Base) : algebraMap Base K r∈S := by
    apply hsimple
    induction r using RatFunc.induction_on with
    | _ p q hq =>
      apply (IntermediateField.mem_adjoin_simple_iff ℚ _).mpr
      exact ⟨p,q,by rw [map_div₀,polynomial_embedding,polynomial_embedding]⟩
  have hold (z : FunctionField.K) : algebraMap FunctionField.K K z∈S := by
    rw [FunctionField.coordinate_expansion z]
    simp only [map_add,map_mul,←IsScalarTower.algebraMap_apply Base FunctionField.K K]
    exact add_mem (add_mem (hbase _) (mul_mem (hbase _) hu))
      (mul_mem (add_mem (hbase _) (mul_mem (hbase _) hu)) hv)
  apply top_unique
  intro z _
  change z∈S
  rw [SecondFunctionField.quadratic_expansion z]
  exact add_mem (hold _) (mul_mem (hold _) hw)

namespace PairOne

theorem m_transcendental : Transcendental ℚ m := by
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base PairOne).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base PairOne (algebraMap ℚ[X] Base p)=aeval m p :=
  generic_polynomial_embedding (algebraMap Base PairOne) p

theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,u,w} : Set PairOne)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,u,w} : Set PairOne)
  have hm : m∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hw : w∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hsimple : IntermediateField.adjoin ℚ ({m} : Set PairOne)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hm
  have hbase (r : Base) : algebraMap Base PairOne r∈S := by
    apply hsimple
    induction r using RatFunc.induction_on with
    | _ p q hq =>
      apply (IntermediateField.mem_adjoin_simple_iff ℚ _).mpr
      exact ⟨p,q,by rw [map_div₀,polynomial_embedding,polynomial_embedding]⟩
  have hfirst (z : FunctionField.First) : algebraMap FunctionField.First PairOne z∈S := by
    rw [SecondFunctionField.quadratic_expansion z,map_add,map_mul,
      ←IsScalarTower.algebraMap_apply Base FunctionField.First PairOne,
      ←IsScalarTower.algebraMap_apply Base FunctionField.First PairOne]
    exact add_mem (hbase _) (mul_mem (hbase _) hu)
  apply top_unique
  intro z _
  change z∈S
  rw [SecondFunctionField.quadratic_expansion z]
  exact add_mem (hfirst _) (mul_mem (hfirst _) hw)

end PairOne

namespace PairTwo

theorem m_transcendental : Transcendental ℚ m := by
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base PairTwo).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base PairTwo (algebraMap ℚ[X] Base p)=aeval m p :=
  generic_polynomial_embedding (algebraMap Base PairTwo) p

theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,u,w} : Set PairTwo)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,u,w} : Set PairTwo)
  have hm : m∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hw : w∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hsimple : IntermediateField.adjoin ℚ ({m} : Set PairTwo)≤S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hm
  have hbase (r : Base) : algebraMap Base PairTwo r∈S := by
    apply hsimple
    induction r using RatFunc.induction_on with
    | _ p q hq =>
      apply (IntermediateField.mem_adjoin_simple_iff ℚ _).mpr
      exact ⟨p,q,by rw [map_div₀,polynomial_embedding,polynomial_embedding]⟩
  have hfirst (z : PairTwoFirst) : algebraMap PairTwoFirst PairTwo z∈S := by
    rw [SecondFunctionField.quadratic_expansion z,map_add,map_mul,
      ←IsScalarTower.algebraMap_apply Base PairTwoFirst PairTwo,
      ←IsScalarTower.algebraMap_apply Base PairTwoFirst PairTwo]
    exact add_mem (hbase _) (mul_mem (hbase _) hu)
  apply top_unique
  intro z _
  change z∈S
  rw [SecondFunctionField.quadratic_expansion z]
  exact add_mem (hfirst _) (mul_mem (hfirst _) hw)

end PairTwo

end
end Z2Z4Rank6.ThirdTwistField
