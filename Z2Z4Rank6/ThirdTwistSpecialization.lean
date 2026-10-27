module

public import Z2Z4Rank6.ThirdTwistSpecialization0
public import Z2Z4Rank6.ThirdTwistSpecialization1
public import Z2Z4Rank6.ThirdTwistSpecialization3

@[expose] public section

/-!
# Four injective specializations for the third twist

The paragraph after Proposition 7.2 in Jaswal, DOI 10.5281/zenodo.23437117.
The specialization theorem used is Theorem 1.1 of Gusić–Tadić.
-/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open Polynomial GusicTadic

theorem twistPolynomial_content (k : Fin 4) : (twistPolynomial k).content=![1,5,5,1] k := by
  fin_cases k <;> norm_num [twistPolynomial,content_mul,q3Poly_content,
    q1Poly_content,q2Poly_content,q12Poly_content]

/-- The criterion-product contents introduce only primes 2,5,7. -/
theorem criterion_content_supported (k : Fin 4) (i : Fin 3) :
    ((twistPolynomial k)^2*rootDifferenceProducts i).content∣(70:ℤ)^8 := by
  rw [twisted_products_content,twistPolynomial_content]
  fin_cases k <;> fin_cases i <;> norm_num

theorem twistPolynomial_ne_zero (k : Fin 4) : twistPolynomial k≠0 := by
  intro h
  have he := congrArg (Polynomial.eval (0:ℤ)) h
  fin_cases k <;> norm_num [twistPolynomial,q3Poly,q3,q1Poly,q2Poly,q12Poly,q1,q2,q12] at he

theorem twist_image_ne_zero (k : Fin 4) : polyToRF (twistPolynomial k)≠0 := by
  intro h
  exact twistPolynomial_ne_zero k (polyToRF_injective (by simpa only [map_zero] using h))

instance generic_elliptic (k : Fin 4) : (genericModel (twistPolynomial k)).IsElliptic :=
  genericModel_elliptic _ (twist_image_ne_zero k)

theorem generic_nonconstant (k : Fin 4) : Nonconstant (genericModel (twistPolynomial k)) :=
  genericModel_nonconstant _ (twist_image_ne_zero k)

instance fiber_elliptic (k : Fin 4) : (fiber k).IsElliptic := by
  have h : (scalingChange (Units.mk0 (scale k) (scale_ne_zero k)) • curve k).IsElliptic :=
    inferInstance
  rw [normalized_scaling] at h
  exact h

theorem roots_divisor_test (k : Fin 4) (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g∣differenceProducts (roots (twistPolynomial k)) i)
    (hn : g.natDegree≠0) : ¬IsSquare (evalAt (parameter k) g) := by
  rw [roots_differenceProducts] at hdiv
  fin_cases k
  · exact Specialization0.divisor_test i g hsq hdiv hn
  · exact Specialization1.divisor_test i g hsq hdiv hn
  · exact Specialization1.divisor_test2 i g hsq hdiv hn
  · exact Specialization3.divisor_test i g hsq hdiv hn

theorem injective_specialization (hGT : GusicTadicTheorem11) (k : Fin 4) :
    InjectiveSpecializationAt (genericModel (twistPolynomial k)) (fiber k) (parameter k) := by
  have hE : ((splitModel (roots (twistPolynomial k))).map polyToRF).IsElliptic := by
    simpa only [←integralModel_split,integralModel_map] using generic_elliptic k
  have hN : Nonconstant ((splitModel (roots (twistPolynomial k))).map polyToRF) := by
    simpa only [←integralModel_split,integralModel_map] using generic_nonconstant k
  have h := hGT (roots (twistPolynomial k)) (parameter k) hE hN (roots_divisor_test k)
  simpa only [←integralModel_split,integralModel_map,integralModel_eval,fiber] using h

theorem injective_normalized_fiber (hGT : GusicTadicTheorem11) (k : Fin 4) :
    ∃σ : (genericModel (twistPolynomial k)).toAffine.Point→+RationalPoints (curve k),
      Function.Injective σ := by
  obtain ⟨σ,_,hσ⟩ := injective_specialization hGT k
  exact ⟨(fiberEquiv k).toAddMonoidHom.comp σ,(fiberEquiv k).injective.comp hσ⟩

theorem generic_rank_le_of_normalized_rank (hGT : GusicTadicTheorem11)
    (k : Fin 4) (n : ℕ) (h : Module.rank ℤ (RationalPoints (curve k))≤n) :
    Module.rank ℤ (genericModel (twistPolynomial k)).toAffine.Point≤n := by
  obtain ⟨σ,hσ⟩ := injective_normalized_fiber hGT k
  exact (σ.toIntLinearMap.rank_le_of_injective hσ).trans h

theorem generic_eq_pointScaling (k : Fin 4) : genericModel (twistPolynomial k)=
    PointScaling.curve (polyToRF (twistPolynomial k)*((a RatFunc.X)^2+(b RatFunc.X)^2))
      ((polyToRF (twistPolynomial k))^2*(a RatFunc.X)^2*(b RatFunc.X)^2) := rfl

end
end Z2Z4Rank6.ThirdTwist
