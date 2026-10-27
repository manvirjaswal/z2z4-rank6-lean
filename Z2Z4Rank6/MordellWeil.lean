import Z2Z4Rank6.BaseCurveArithmetic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# The Mordell--Weil theorem

J. H. Silverman, The Arithmetic of Elliptic Curves, second edition,
GTM 106 (2009), Theorem VIII.4.1, p. 220.
-/

namespace Z2Z4Rank6

/-- Every rational elliptic curve has a finitely generated
rational point group, as in the Mordell--Weil theorem. -/
def MordellWeilTheorem : Prop :=
  ∀ W : WeierstrassCurve ℚ, GoodCurve W → AddGroup.FG (RationalPoints W)

/-- The ordinary rank lower bound on E_C follows from the printed point of
infinite order. It does not use a rank upper bound or a Selmer computation. -/
theorem ec_rank_at_least_one (hSilvermanVII34 : OddPrimeTorsionIntegrality) :
    1 ≤ Module.rank ℤ (RationalPoints EC) := by
  rw [Cardinal.one_le_iff_ne_zero]
  intro hzero
  have ht := (Module.rank_eq_zero_iff_isTorsion (R := ℤ)
    (M := RationalPoints EC)).mp hzero
  have hA : IsAddTorsion (RationalPoints EC) := isAddTorsion_iff_isTorsion_int.mpr ht
  exact ecP_infinite_order hSilvermanVII34 (hA ecP)

end Z2Z4Rank6
