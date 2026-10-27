import Z2Z4Rank6.TwistSelmerData
import Z2Z4Rank6.GusicTadicSpecialization
import Z2Z4Rank6.VariableChangePoints
import Z2Z4Rank6.SplitTwoTorsion
import Z2Z4Rank6.RankModTwo
import Z2Z4Rank6.MordellWeil

/-!
# Point-group rank transport for the three twist fibers

The normalizations and specializations in Proposition 5.2 of Jaswal,
DOI 10.5281/zenodo.23437117, are additive equivalences and injective
homomorphisms. This file proves their rank consequences for arbitrary upper
bounds; the concrete finite certificates are supplied separately.
-/

namespace Z2Z4Rank6.TwistSelmer
noncomputable section

def fiberEquiv (k : Fin 3) :
    RationalPoints (GusicTadic.fiberModel (twistPolynomial k) (parameter k)) ≃+
      RationalPoints (curve k) :=
  (PointScaling.pointCongr (normalized_scaling k).symm).trans
    (VariableChangePoints.pointEquiv (curve k)
      (scalingChange (Units.mk0 (scale k) (scale_ne_zero k))))

theorem fullTwoTorsion_inclusion (k : Fin 3) :
    ∃ j : (ZMod 2 × ZMod 2) →+ RationalPoints (curve k), Function.Injective j := by
  let : (SplitTwoTorsion.curve (r2 k : ℚ) (r3 k : ℚ)).IsElliptic := by
    change (curve k).IsElliptic
    infer_instance
  exact SplitTwoTorsion.inclusion (r2 k : ℚ) (r3 k : ℚ)
    (by exact_mod_cast (roots_nonzero_distinct k).1)

theorem injective_to_normalized_fiber (hGT : GusicTadic.GusicTadicTheorem11) (k : Fin 3) :
    ∃ σ : (GusicTadic.genericModel (twistPolynomial k)).toAffine.Point →+
      RationalPoints (curve k), Function.Injective σ := by
  have hs : GusicTadic.InjectiveSpecializationAt
      (GusicTadic.genericModel (twistPolynomial k))
      (GusicTadic.fiberModel (twistPolynomial k) (parameter k)) (parameter k) := by
    fin_cases k
    · exact GusicTadic.q1_injective_specialization_14 hGT
    · exact GusicTadic.q2_injective_specialization_50 hGT
    · exact GusicTadic.q12_injective_specialization_50 hGT
  obtain ⟨σ,_,hσ⟩ := hs
  exact ⟨(fiberEquiv k).toAddMonoidHom.comp σ,(fiberEquiv k).injective.comp hσ⟩

theorem generic_rank_le_of_normalized_rank (hGT : GusicTadic.GusicTadicTheorem11)
    (k : Fin 3) (n : ℕ) (h : Module.rank ℤ (RationalPoints (curve k))≤n) :
    Module.rank ℤ (GusicTadic.genericModel (twistPolynomial k)).toAffine.Point≤n := by
  obtain ⟨σ,hσ⟩ := injective_to_normalized_fiber hGT k
  exact (σ.toIntLinearMap.rank_le_of_injective hσ).trans h

end
end Z2Z4Rank6.TwistSelmer
