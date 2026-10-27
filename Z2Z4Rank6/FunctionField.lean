import Z2Z4Rank6.Twists
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The degree-four function field of C

The curve C in Manvir Jaswal, *Infinitely many elliptic curves with torsion
Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117, equations (1.3) and Proposition 4.2,
has function field Q(m,u,v), with u²=5(3m²+242), v²=5(2m²+243).

We construct the field as a tower of two quadratic root algebras. Rational-function nonsquares are
detected by the
nonsquare leading coefficients 15, 10 and 150 in Q; integral closedness shows
that a rational-function square root of a polynomial would be a polynomial.
-/

namespace Z2Z4Rank6.FunctionField

open Polynomial

noncomputable section

/-- A polynomial with nonsquare leading coefficient cannot become a square in
the rational-function field. -/
theorem not_isSquare_fraction_of_leadingCoeff {F : Type*} [Field F]
    (p : F[X]) (hp : ¬ IsSquare p.leadingCoeff) :
    ¬ IsSquare (algebraMap F[X] (RatFunc F) p) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral F[X] (z^2) := by
    rw [sq, ← hz]
    exact isIntegral_algebraMap
  obtain ⟨r, hr⟩ :=
    IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := F[X])
      (by decide : 0 < (2 : ℕ)) hint
  have heq : p = r*r := by
    apply RatFunc.algebraMap_injective F
    simpa only [map_mul, hr] using hz
  apply hp
  exact ⟨r.leadingCoeff, by rw [heq, leadingCoeff_mul]⟩

/-- The first polynomial defining C, regarded in Q[m]. -/
def firstPolynomial : ℚ[X] := 5*(3*Polynomial.X^2+242)
/-- The second polynomial defining C, regarded in Q[m]. -/
def secondPolynomial : ℚ[X] := 5*(2*Polynomial.X^2+243)

private theorem firstPolynomial_leadingCoeff : firstPolynomial.leadingCoeff = 15 := by
  have heq : firstPolynomial = C 15*Polynomial.X^2+C 0*Polynomial.X+C 1210 := by
    norm_num only [firstPolynomial, Polynomial.C_ofNat, Polynomial.C_0]
    ring
  rw [heq, leadingCoeff_quadratic (by norm_num)]

private theorem secondPolynomial_leadingCoeff : secondPolynomial.leadingCoeff = 10 := by
  have heq : secondPolynomial = C 10*Polynomial.X^2+C 0*Polynomial.X+C 1215 := by
    norm_num only [secondPolynomial, Polynomial.C_ofNat, Polynomial.C_0]
    ring
  rw [heq, leadingCoeff_quadratic (by norm_num)]

/-- The rational function field Q(m). -/
abbrev Base := RatFunc ℚ

/-- A fixed equality decision for the rational-function coefficient field. -/
instance baseDecidableEq : DecidableEq Base := Classical.decEq Base

/-- The first square class, exactly as printed in equation (1.3). -/
def d1 : Base := q1 (RatFunc.X^2)
/-- The second square class, exactly as printed in equation (1.3). -/
def d2 : Base := q2 (RatFunc.X^2)

private theorem firstPolynomial_image : algebraMap ℚ[X] Base firstPolynomial = d1 := by
  simp [firstPolynomial, d1, q1, RatFunc.algebraMap_X, map_ofNat]

private theorem secondPolynomial_image : algebraMap ℚ[X] Base secondPolynomial = d2 := by
  simp [secondPolynomial, d2, q2, RatFunc.algebraMap_X, map_ofNat]

/-- q1 is nonsquare in Q(m). -/
theorem d1_not_isSquare : ¬ IsSquare d1 := by
  rw [← firstPolynomial_image]
  apply not_isSquare_fraction_of_leadingCoeff
  rw [firstPolynomial_leadingCoeff]
  norm_num

/-- q2 is nonsquare in Q(m). -/
theorem d2_not_isSquare : ¬ IsSquare d2 := by
  rw [← secondPolynomial_image]
  apply not_isSquare_fraction_of_leadingCoeff
  rw [secondPolynomial_leadingCoeff]
  norm_num

/-- The product q1*q2 is nonsquare in Q(m), so the two square classes
are independent. -/
theorem d1_mul_d2_not_isSquare : ¬ IsSquare (d1*d2) := by
  rw [← firstPolynomial_image, ← secondPolynomial_image, ← map_mul]
  apply not_isSquare_fraction_of_leadingCoeff
  rw [leadingCoeff_mul, firstPolynomial_leadingCoeff, secondPolynomial_leadingCoeff]
  norm_num

/-- In a quadratic root algebra, a scalar e is nonsquare when both e and d*e
are nonsquare in the coefficient field. The proof compares the two coefficients
of (x+y√d)². -/
theorem not_isSquare_in_quadratic {F : Type*} [Field F] [CharZero F]
    (d e : F) (he : ¬ IsSquare e) (hde : ¬ IsSquare (d*e)) :
    ¬ IsSquare (algebraMap F (QuadraticAlgebra F d 0) e) := by
  rintro ⟨z, hz⟩
  have hre : e = z.re*z.re+d*z.im*z.im := by
    simpa only [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul] using
      congrArg QuadraticAlgebra.re hz
  have him : 0 = z.re*z.im+z.im*z.re := by
    simpa only [QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul,
      zero_mul, add_zero] using congrArg QuadraticAlgebra.im hz
  have hprod : z.re*z.im = 0 := by
    have h2 : (2 : F)*(z.re*z.im) = 0 := by linear_combination -him
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hprod with hr | hi
  · apply hde
    refine ⟨d*z.im, ?_⟩
    rw [hr, zero_mul, zero_add] at hre
    rw [hre]
    ring
  · apply he
    refine ⟨z.re, ?_⟩
    simpa only [hi, mul_zero, add_zero] using hre

instance d1_nonsquare_fact : Fact (¬ IsSquare d1) := ⟨d1_not_isSquare⟩

/-- The first quadratic function field Q(m,u), where u²=q1. -/
abbrev First := QuadraticAlgebra Base d1 0

/-- The second defining square class, mapped into Q(m,u). -/
def d2First : First := algebraMap Base First d2

/-- q2 remains nonsquare after adjoining sqrt(q1). -/
theorem d2First_not_isSquare : ¬ IsSquare d2First :=
  not_isSquare_in_quadratic d1 d2 d2_not_isSquare d1_mul_d2_not_isSquare

instance d2First_nonsquare_fact : Fact (¬ IsSquare d2First) := ⟨d2First_not_isSquare⟩

/-- The function field Q(m,u,v). -/
abbrev K := QuadraticAlgebra First d2First 0

/-- The transcendental parameter m in Q(C). -/
def m : K := algebraMap Base K RatFunc.X
/-- The first square root u in Q(C). -/
def u : K := algebraMap First K (QuadraticAlgebra.omega : First)
/-- The second square root v in Q(C). -/
def v : K := QuadraticAlgebra.omega

/-- The first defining equation of C holds in its constructed field. -/
theorem u_sq : u^2 = 5*(3*m^2+242) := by
  rw [u, ← map_pow]
  have hroot : (QuadraticAlgebra.omega : First)^2 = algebraMap Base First d1 := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hroot, ← IsScalarTower.algebraMap_apply Base First K]
  simp [d1, q1, m, map_ofNat]

/-- The second defining equation of C holds in its constructed field. -/
theorem v_sq : v^2 = 5*(2*m^2+243) := by
  have hroot : v^2 = algebraMap First K d2First := by
    rw [v, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero, zero_mul, add_zero]
  calc
    v^2 = algebraMap First K d2First := hroot
    _ = algebraMap Base K d2 := (IsScalarTower.algebraMap_apply Base First K d2).symm
    _ = 5*(2*m^2+243) := by simp [d2, q2, m, map_ofNat]

/-- Q(m,u) has degree two over Q(m). -/
theorem first_finrank : Module.finrank Base First = 2 :=
  QuadraticAlgebra.finrank_eq_two d1 0

/-- Q(C) has degree two over Q(m,u). -/
theorem second_finrank : Module.finrank First K = 2 :=
  QuadraticAlgebra.finrank_eq_two d2First 0

/-- The constructed Q(C) has degree four over Q(m). -/
theorem finrank_eq_four : Module.finrank Base K = 4 := by
  rw [← Module.finrank_mul_finrank Base First K, first_finrank, second_finrank]

/-- The explicit four-element tower basis, with entries 1,v,u,uv in product
index order. -/
def basis : Module.Basis (Fin 2 × Fin 2) Base K :=
  (QuadraticAlgebra.basis d1 0).smulTower (QuadraticAlgebra.basis d2First 0)

/-- m is transcendental over Q in the constructed function field. -/
theorem m_transcendental : Transcendental ℚ m := by
  apply (transcendental_algebraMap_iff (R := ℚ)
    (algebraMap Base K).injective).mpr
  convert RatFunc.transcendental_X (K := ℚ) using 1
  exact Subsingleton.elim _ _

/-- Every element has a unique coordinate expansion in 1,u,v,uv. This is the
explicit algebraic presentation of the field extension. -/
theorem coordinate_expansion (z : K) :
    z = (algebraMap Base K z.re.re + algebraMap Base K z.re.im*u) +
      (algebraMap Base K z.im.re + algebraMap Base K z.im.im*u)*v := by
  have hfirst (w : First) : w = algebraMap Base First w.re +
      algebraMap Base First w.im*(QuadraticAlgebra.omega : First) := by
    simpa only [Algebra.smul_def, mul_one] using
      (QuadraticAlgebra.re_smul_add_im_smul w).symm
  have hmap (w : First) : algebraMap First K w =
      algebraMap Base K w.re+algebraMap Base K w.im*u := by
    have hw := congrArg (algebraMap First K) (hfirst w)
    simpa only [map_add, map_mul, ← IsScalarTower.algebraMap_apply Base First K, u] using hw
  have hz : z = algebraMap First K z.re+algebraMap First K z.im*v := by
    simpa only [Algebra.smul_def, mul_one, v] using
      (QuadraticAlgebra.re_smul_add_im_smul z).symm
  calc
    z = algebraMap First K z.re+algebraMap First K z.im*v := hz
    _ = _ := by rw [hmap z.re, hmap z.im]

/-- The constructed field is generated over Q(m) by the two printed
square roots; it contains no additional algebraic elements. -/
theorem algebra_adjoin_roots_eq_top : Algebra.adjoin Base ({u,v} : Set K) = ⊤ := by
  apply Algebra.eq_top_iff.mpr
  intro z
  rw [coordinate_expansion z]
  have hu : u ∈ Algebra.adjoin Base ({u,v} : Set K) :=
    Algebra.subset_adjoin (by simp)
  have hv : v ∈ Algebra.adjoin Base ({u,v} : Set K) :=
    Algebra.subset_adjoin (by simp)
  exact add_mem
    (add_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (Subalgebra.algebraMap_mem _ _) hu))
    (mul_mem (add_mem (Subalgebra.algebraMap_mem _ _)
      (mul_mem (Subalgebra.algebraMap_mem _ _) hu)) hv)

/-- Polynomial evaluation at m agrees with the embedding of Q[m] through
Q(m), including its coefficient map. -/
theorem polynomial_embedding (p : ℚ[X]) :
    algebraMap Base K (algebraMap ℚ[X] Base p) = aeval m p := by
  have hC : (algebraMap Base K).comp (RatFunc.C : ℚ →+* Base) = algebraMap ℚ K :=
    Subsingleton.elim _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n r =>
    have hr := RingHom.congr_fun hC r
    simp only [RingHom.comp_apply] at hr
    simp only [RatFunc.algebraMap_monomial, map_mul, map_pow, aeval_monomial, m, hr]

/-- The field is exactly the field Q(m,u,v), generated by the three
printed coordinates over Q. -/
theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,u,v} : Set K) = ⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,u,v} : Set K)
  have hm : m ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hu : u ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hv : v ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hsimple : IntermediateField.adjoin ℚ ({m} : Set K) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ hm
  have hbase (r : Base) : algebraMap Base K r ∈ S := by
    apply hsimple
    induction r using RatFunc.induction_on with
    | _ p q hq =>
      apply (IntermediateField.mem_adjoin_simple_iff ℚ _).mpr
      exact ⟨p,q, by rw [map_div₀, polynomial_embedding, polynomial_embedding]⟩
  apply top_unique
  intro z _
  change z ∈ S
  rw [coordinate_expansion z]
  exact add_mem (add_mem (hbase _) (mul_mem (hbase _) hu))
    (mul_mem (add_mem (hbase _) (mul_mem (hbase _) hu)) hv)

/-- The first root relation expressed through the coefficient embedding. -/
theorem u_sq_eq_d1 : u^2 = algebraMap Base K d1 := by
  rw [u, ← map_pow]
  have hroot : (QuadraticAlgebra.omega : First)^2 = algebraMap Base First d1 := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hroot, ← IsScalarTower.algebraMap_apply Base First K]

/-- The second root relation expressed through the coefficient embedding. -/
theorem v_sq_eq_d2 : v^2 = algebraMap Base K d2 := by
  calc
    v^2 = algebraMap First K d2First := by
      rw [v, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp only [map_zero, zero_mul, add_zero]
    _ = algebraMap Base K d2 := (IsScalarTower.algebraMap_apply Base First K d2).symm

/-- The function m is nonzero in Q(C). -/
theorem m_ne_zero : m ≠ 0 := by
  intro h
  apply RatFunc.X_ne_zero (K := ℚ)
  apply (algebraMap Base K).injective
  simpa only [map_zero, m] using h

/-- The first square root is nonzero in Q(C). -/
theorem u_ne_zero : u ≠ 0 := by
  intro h
  apply d1_not_isSquare
  refine ⟨0, ?_⟩
  apply (algebraMap Base K).injective
  rw [← u_sq_eq_d1, h]
  simp

/-- The second square root is nonzero in Q(C). -/
theorem v_ne_zero : v ≠ 0 := by
  intro h
  apply d2_not_isSquare
  refine ⟨0, ?_⟩
  apply (algebraMap Base K).injective
  rw [← v_sq_eq_d2, h]
  simp

private def fiberProductPolynomial : ℚ[X] :=
  a Polynomial.X*b Polynomial.X*((a Polynomial.X)^2-(b Polynomial.X)^2)

private theorem fiberProductPolynomial_ne_zero : fiberProductPolynomial ≠ 0 := by
  intro h
  have heval := congrArg (Polynomial.eval (2 : ℚ)) h
  norm_num [fiberProductPolynomial, a, b] at heval

/-- The generic fiber has nonzero ab(a²-b²) in the constructed field. -/
theorem fiber_product_ne_zero : a m*b m*((a m)^2-(b m)^2) ≠ 0 := by
  have hinj := transcendental_iff_injective.mp m_transcendental
  have heval : aeval m fiberProductPolynomial = a m*b m*((a m)^2-(b m)^2) := by
    simp [fiberProductPolynomial, a, b, map_ofNat]
  intro h
  apply fiberProductPolynomial_ne_zero
  apply hinj
  simpa only [map_zero, heval] using h

/-- The family X over this function field is an elliptic curve. -/
instance genericFiberElliptic : (X m).IsElliptic := by
  have ha : a m ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).1
  have hb : b m ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).2
  have hab : (a m)^2-(b m)^2 ≠ 0 := (mul_ne_zero_iff.mp fiber_product_ne_zero).2
  have hdisc : (X m).Δ = 16*(a m)^4*(b m)^4*((a m)^2-(b m)^2)^2 := by
    simp only [X, E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  constructor
  rw [isUnit_iff_ne_zero, hdisc]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))
    (pow_ne_zero _ hb)) (pow_ne_zero _ hab)

set_option maxHeartbeats 1000000 in
/-- The six printed points as elements of the generic elliptic point
group X(Q(C)). This statement asserts their coordinates and membership; their
independence is a separate theorem. -/
def points : Fin 6 → (X m).toAffine.Point :=
  sixPoints m u v u_sq v_sq m_ne_zero u_ne_zero v_ne_zero

end
end Z2Z4Rank6.FunctionField
