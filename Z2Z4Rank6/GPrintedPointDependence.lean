import Z2Z4Rank6.GExactRank

/-!
# Dependence of the omitted transformed section over G

The final sentence of Proposition 7.2(b) in Jaswal,
DOI 10.5281/zenodo.23437117, says that the transformed P1 is dependent
on P1,P2,P3,P2',P3'. Here P1' is the point with the printed
transformed coordinates. Finite index gives a positive multiple in the
integer span of the five specified points, hence a relation whose P1'
coefficient is nonzero.
-/
namespace Z2Z4Rank6.GFunctionField
noncomputable section

def p1PrimeX : K := (delta m eta)^4*p1x (mPrime m eta)
def p1PrimeY : K := (delta m eta)^6*p1y (mPrime m eta)

theorem p1Prime_equation : (X m).toAffine.Equation p1PrimeX p1PrimeY := by
  exact (E_equation_iff_factored _ _ _ _).2
    (transformed_equation m eta _ _ eta_sq chart_denominator_ne_zero
      chart_numerator_ne_zero (p1_equation (mPrime m eta)))

/-- The image of P1 under the transformation used to define P2',P3'. -/
def p1Prime : (X m).toAffine.Point := .mk p1Prime_equation

theorem encode_p1Prime :
    Common.WeierstrassCoordinates.encode p1Prime=some (p1PrimeX,p1PrimeY) := rfl

abbrev printedSpan : Submodule ℤ (X m).toAffine.Point :=
  Submodule.span ℤ (Set.range points)

/-- The coefficient of the transformed P1 is a nonzero natural
number, so this is a dependence on the other five sections. -/
theorem p1Prime_multiple_mem_span (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11)
    (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    ∃n : ℕ,n≠0 ∧ n • p1Prime∈printedSpan := by
  have hIndex := GExactRank.printed_five_finite_index
    hMazur hMW hDescent hReduction hFormal hGT hMWLN
  obtain ⟨n,hn,_,hmem⟩ := printedSpan.toAddSubgroup.exists_nsmul_mem_of_index_ne_zero
    hIndex.index_ne_zero p1Prime
  exact ⟨n,hn.ne',hmem⟩

/-- An explicit finite integral relation, with nonzero coefficient on P1'. -/
theorem p1Prime_integral_relation (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11)
    (hMWLN : MordellWeilLangNeronTheorem.{0}) :
    ∃n : ℕ,n≠0 ∧ ∃c : Fin 5→ℤ,(n:ℤ) • p1Prime=∑i,c i • points i := by
  obtain ⟨n,hn,hmem⟩ :=
    p1Prime_multiple_mem_span hMazur hMW hDescent hReduction hFormal hGT hMWLN
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  exact ⟨n,hn,c,(Nat.cast_smul_eq_nsmul ℤ n p1Prime).trans hc.symm⟩

def sixTransformedPoints : Fin 6→(X m).toAffine.Point := Fin.cons p1Prime points

/-- The six-point tuple is dependent in the Q(G) group. -/
theorem sixTransformedPoints_dependent (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hReduction : GoodReductionHomomorphisms) (hFormal : FormalGoodReductionHomomorphisms)
    (hGT : GusicTadic.GusicTadicTheorem11) :
    ¬LinearIndependent ℤ sixTransformedPoints := by
  intro hLI
  have hle : (6 : Cardinal)≤Module.rank ℤ (X m).toAffine.Point := by
    simpa using hLI.cardinal_lift_le_rank
  rw [GExactRank.rank_eq_five hMazur hMW hDescent hReduction hFormal hGT] at hle
  norm_num at hle

end
end Z2Z4Rank6.GFunctionField
