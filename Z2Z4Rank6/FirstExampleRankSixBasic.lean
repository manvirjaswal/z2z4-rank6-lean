module

public import Z2Z4Rank6.TwoDescent
public import Z2Z4Rank6.Torsion
public import Z2Z4Rank6.ReductionData

@[expose] public section

/-! The coprime integral model at c₀ from Proposition 5.1 and the
unnumbered exact-rank assertion before Proposition 6.2 of Jaswal,
DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.FirstExampleRankSix

def A : ℚ := 7037226227200
def B : ℚ := 3329722383911
abbrev curve : WeierstrassCurve ℚ := E A B

theorem factor_nonzero : A*B*(A^2-B^2)≠0 := by norm_num [A,B]
instance curveElliptic : curve.IsElliptic := E_good A B factor_nonzero

theorem printed_parameters : A=(ReductionData.a0:ℚ) ∧ B=(ReductionData.b0:ℚ) := by
  norm_num [A,B,ReductionData.a0,ReductionData.b0]

end Z2Z4Rank6.FirstExampleRankSix
