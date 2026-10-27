module

public import Z2Z4Rank6.FunctionField
public import Z2Z4Rank6.PointMap

@[expose] public section

/-!
# The two sign automorphisms of Q(C)

The field and point-group involutions underlying Remark 4.3 of
Manvir Jaswal, DOI 10.5281/zenodo.23437117. They are constructed
on the explicit quadratic tower and act by the printed sign changes of u,v.
-/

namespace Z2Z4Rank6.FunctionField

noncomputable section

/-- Conjugation in Q(m,u), fixing Q(m) and sending u to -u. -/
def firstConjugation : First ≃ₐ[Base] First :=
  { starRingAut with
    commutes' := by
      intro c
      apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem firstConjugation_apply (z : First) : firstConjugation z = star z := rfl

@[simp] theorem firstConjugation_involutive (z : First) :
    firstConjugation (firstConjugation z) = z := by
  change star (star z) = z
  exact star_star z

@[simp] theorem firstConjugation_d2 : firstConjugation d2First = d2First :=
  firstConjugation.commutes d2

/-- The Q(m)-automorphism changing the sign of u and fixing v. -/
def sigmaU : K ≃ₐ[Base] K where
  toFun z := ⟨firstConjugation z.re,firstConjugation z.im⟩
  invFun z := ⟨firstConjugation z.re,firstConjugation z.im⟩
  left_inv z := by apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _
  right_inv z := by apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _
  map_add' z w := by apply QuadraticAlgebra.ext <;> simp
  map_mul' z w := by
    apply QuadraticAlgebra.ext <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
        map_add, map_mul, map_zero, firstConjugation_d2]
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply Base First K]
    apply QuadraticAlgebra.ext
    · exact firstConjugation.commutes c
    · simp

/-- The Q(m)-automorphism changing the sign of v and fixing u. -/
def sigmaV : K ≃ₐ[Base] K :=
  { starRingAut with
    commutes' := by
      intro c
      rw [IsScalarTower.algebraMap_apply Base First K]
      apply QuadraticAlgebra.ext <;> simp }

@[simp] theorem sigmaV_apply (z : K) : sigmaV z = star z := rfl

@[simp] theorem sigmaU_base (r : Base) : sigmaU (algebraMap Base K r) = algebraMap Base K r :=
  sigmaU.commutes r

@[simp] theorem sigmaV_base (r : Base) : sigmaV (algebraMap Base K r) = algebraMap Base K r :=
  sigmaV.commutes r

@[simp] theorem sigmaU_m : sigmaU m = m := sigmaU.commutes RatFunc.X
@[simp] theorem sigmaV_m : sigmaV m = m := sigmaV.commutes RatFunc.X

@[simp] theorem sigmaU_u : sigmaU u = -u := by
  apply QuadraticAlgebra.ext <;>
    simp [sigmaU, u, QuadraticAlgebra.omega]

@[simp] theorem sigmaU_v : sigmaU v = v := by
  apply QuadraticAlgebra.ext <;>
    simp [sigmaU, v, QuadraticAlgebra.omega]

@[simp] theorem sigmaV_u : sigmaV u = u := by
  apply QuadraticAlgebra.ext <;> simp [u]

@[simp] theorem sigmaV_v : sigmaV v = -v := by
  apply QuadraticAlgebra.ext <;> simp [v, QuadraticAlgebra.omega]

/-- The first field automorphism is an involution. -/
theorem sigmaU_involutive (z : K) : sigmaU (sigmaU z) = z := by
  apply QuadraticAlgebra.ext <;> exact firstConjugation_involutive _

/-- The second field automorphism is an involution. -/
theorem sigmaV_involutive (z : K) : sigmaV (sigmaV z) = z := by
  change star (star z) = z
  exact star_star z

/-- The two printed sign changes commute on the function field. -/
theorem sigmaU_sigmaV_commute (z : K) : sigmaU (sigmaV z) = sigmaV (sigmaU z) := by
  apply QuadraticAlgebra.ext <;> simp [sigmaU]

private theorem eq_zero_of_neg_eq {F : Type*} [Field F] [CharZero F]
    {z : F} (h : -z=z) : z=0 := by
  have h2 : (2 : F)*z=0 := by linear_combination -h
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The elements fixed by both sign automorphisms are exactly
the embedded rational-function coefficient field Q(m). The scalar witness is
the first coordinate of the explicit four-element tower basis. -/
theorem fixed_iff_in_base (z : K) :
    (sigmaU z=z ∧ sigmaV z=z) ↔ ∃ b : Base, algebraMap Base K b=z := by
  constructor
  · rintro ⟨hU,hV⟩
    have him : z.im=0 := by
      have h := congrArg QuadraticAlgebra.im hV
      change -z.im=z.im at h
      exact eq_zero_of_neg_eq h
    have hreim : z.re.im=0 := by
      have h := congrArg (fun w : K => w.re.im) hU
      change -(z.re.im)=z.re.im at h
      exact eq_zero_of_neg_eq h
    refine ⟨z.re.re, ?_⟩
    rw [IsScalarTower.algebraMap_apply Base First K]
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · rfl
      · change 0=z.re.im
        exact hreim.symm
    · change 0=z.im
      exact him.symm
  · rintro ⟨b,rfl⟩
    exact ⟨sigmaU_base b,sigmaV_base b⟩

/-- A fixed field element has a coefficient in Q(m). -/
theorem exists_base_of_fixed (z : K) (hU : sigmaU z=z) (hV : sigmaV z=z) :
    ∃ b : Base, algebraMap Base K b=z :=
  (fixed_iff_in_base z).mp ⟨hU,hV⟩

end
end Z2Z4Rank6.FunctionField
