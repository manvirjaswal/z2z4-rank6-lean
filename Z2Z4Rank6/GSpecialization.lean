module

public import Z2Z4Rank6.GSpecializationDivisors
public import Z2Z4Rank6.GusicTadicSpecialization

@[expose] public section

/-!
# Injective specialization of the h-twist at m=-80/3

The Gusić–Tadić step in Proposition 7.2(b) of Jaswal,
DOI: 10.5281/zenodo.23437117. All integral factorization and universal
squarefree-divisor hypotheses are proved. The hypothesis is Theorem 1.1 of Gusić–Tadić.
-/

namespace Z2Z4Rank6.GSpecialization

open Polynomial GusicTadic
noncomputable section

theorem hPoly_image_ne_zero : polyToRF hPoly ≠ 0 := by
  intro h
  exact hPoly_ne_zero (polyToRF_injective (by simpa only [map_zero] using h))

theorem h_generic_elliptic : (genericModel hPoly).IsElliptic :=
  genericModel_elliptic hPoly hPoly_image_ne_zero

theorem h_nonconstant : Nonconstant (genericModel hPoly) :=
  genericModel_nonconstant hPoly hPoly_image_ne_zero

theorem h_fiber_elliptic : GTwistSelmer.fiber.IsElliptic := by
  have h : (scalingChange (Units.mk0 GTwistSelmer.scale GTwistSelmer.scale_ne_zero) •
      GTwistSelmer.curve).IsElliptic := inferInstance
  rw [GTwistSelmer.normalized_scaling] at h
  exact h

theorem h_roots_divisor_test (i : Fin 3) (g : ℤ[X])
    (hsq : Squarefree g) (hdiv : g ∣ differenceProducts (roots hPoly) i)
    (hnonconstant : g.natDegree≠0) : ¬IsSquare (evalAt parameter g) := by
  rw [roots_differenceProducts] at hdiv
  exact divisor_test i g hsq hdiv hnonconstant

/-- Canonical specialization on the h-twist point group is injective
at the printed parameter, using only the published GT theorem. -/
theorem h_injective_specialization (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel hPoly) GTwistSelmer.fiber parameter := by
  have hE : ((splitModel (roots hPoly)).map polyToRF).IsElliptic := by
    simpa only [←integralModel_split,integralModel_map] using h_generic_elliptic
  have hN : Nonconstant ((splitModel (roots hPoly)).map polyToRF) := by
    simpa only [←integralModel_split,integralModel_map] using h_nonconstant
  have h := hGT (roots hPoly) parameter hE hN h_roots_divisor_test
  simpa only [←integralModel_split,integralModel_map,integralModel_eval,GTwistSelmer.fiber] using h

theorem h_injective_specialization_neg80 (hGT : GusicTadicTheorem11) :
    InjectiveSpecializationAt (genericModel GTwistSelmer.hPolynomial)
      (fiberModel GTwistSelmer.hPolynomial (-80/3)) (-80/3) := by
  simpa only [GTwistSelmer.fiber,hPoly,parameter,GTwistSelmer.parameter] using h_injective_specialization hGT

/-- Composing with the proved rational scaling gives an injective
homomorphism into the normalized integer fiber used for the Selmer bound. -/
theorem h_injective_normalized_fiber (hGT : GusicTadicTheorem11) :
    ∃ σ : (genericModel hPoly).toAffine.Point →+ RationalPoints GTwistSelmer.curve,
      Function.Injective σ := by
  obtain ⟨σ, _, hσ⟩ := h_injective_specialization hGT
  exact ⟨GTwistSelmer.fiberEquiv.toAddMonoidHom.comp σ,
    GTwistSelmer.fiberEquiv.injective.comp hσ⟩

end
end Z2Z4Rank6.GSpecialization
