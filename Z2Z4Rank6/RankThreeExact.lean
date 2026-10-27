import Z2Z4Rank6.RankThreeSelmerCertificate
import Z2Z4Rank6.RankThreeGeneric
import Z2Z4Rank6.GusicTadicSpecialization
import Z2Z4Rank6.PointScaling

/-!
# Exact rank three of the original rational-function family

Proposition 2.3 of M. Jaswal, DOI 10.5281/zenodo.23437117. The printed
14/3 fiber is identified by the scaling of its elliptic point group
with E3747769,2090231. Its checked complete-descent image has at most 32
classes. The published Gusić--Tadić injective specialization theorem then
bounds the original Q(m)-rank by 3; the three printed independent sections
supply the reverse bound.
-/

namespace Z2Z4Rank6.RankThreeExact

noncomputable section

/-- The printed rational coefficient scaling at m=14/3. -/
theorem parameter_scaling :
    a (14/3 : ℚ)=(7/81 : ℚ)*RankThreeSelmer.A ∧
      b (14/3 : ℚ)=(7/81 : ℚ)*RankThreeSelmer.B := by
  norm_num [a,b,RankThreeSelmer.A,RankThreeSelmer.B]

private def coeffA : ℚ := (a (14/3 : ℚ))^2+(b (14/3 : ℚ))^2
private def coeffB : ℚ := (a (14/3 : ℚ))^2*(b (14/3 : ℚ))^2

private theorem scaled_curve :
    PointScaling.curve ((81/7 : ℚ)^2*coeffA) ((81/7 : ℚ)^4*coeffB)=
      RankThreeSelmer.curve := by
  ext <;> norm_num [PointScaling.curve,coeffA,coeffB,RankThreeSelmer.curve,
    E,a,b,RankThreeSelmer.A,RankThreeSelmer.B]

/-- The printed scaling is an additive equivalence between
rational elliptic point groups. -/
def fiberEquiv : RationalPoints (X (14/3 : ℚ)) ≃+
    RationalPoints RankThreeSelmer.curve :=
  (PointScaling.pointCongr (show X (14/3 : ℚ)=PointScaling.curve coeffA coeffB from rfl)).trans
    ((PointScaling.scaleEquiv coeffA coeffB (81/7 : ℚ) (by norm_num)).trans
      (PointScaling.pointCongr scaled_curve))

/-- The original fiber at 14/3 has integral rank at most 3. -/
theorem fiber_rank_at_most_three (hMW : MordellWeilTheorem)
    (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ (RationalPoints (X (14/3 : ℚ)))≤3 := by
  calc
    Module.rank ℤ (RationalPoints (X (14/3 : ℚ))) =
        Module.rank ℤ (RationalPoints RankThreeSelmer.curve) := fiberEquiv.toIntLinearEquiv.rank_eq
    _ ≤ 3 := RankThreeSelmer.curve_rank_at_most_three hMW hDescent

end
end Z2Z4Rank6.RankThreeExact

namespace Z2Z4Rank6.RationalFunctionFamily

/-- The checked 14/3 fiber bound and injective specialization bound the
original Q(m) point-group rank above by 3. -/
theorem rank_at_most_three (hGT : GusicTadic.GusicTadicTheorem11)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem) :
    Module.rank ℤ curve.toAffine.Point≤3 := by
  obtain ⟨spec,_,hspec⟩ := GusicTadic.X_injective_specialization_14 hGT
  exact (spec.toIntLinearMap.rank_le_of_injective hspec).trans
    (RankThreeExact.fiber_rank_at_most_three hMW hDescent)

/-- Proposition 2.3 as printed, the original curve over Q(m)
has integral Mordell--Weil rank exactly 3. -/
theorem rank_eq_three (hMazur : MazurTorsionTheorem)
    (hMW : MordellWeilTheorem) (hDescent : CompleteTwoDescentTheorem)
    (hFormal : FormalGoodReductionHomomorphisms) (hGT : GusicTadic.GusicTadicTheorem11) :
    Module.rank ℤ curve.toAffine.Point=3 := by
  apply le_antisymm (rank_at_most_three hGT hMW hDescent)
  simpa using (points_linearIndependent hMazur hDescent hFormal).cardinal_lift_le_rank

end Z2Z4Rank6.RationalFunctionFamily
