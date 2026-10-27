import Z2Z4Rank6.FunctionField
import Z2Z4Rank6.BaseCurve
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LaurentSeries

/-!
# Formal local coordinates at c0

This constructs the power-series square roots used to embed the
function field of C into Q((T)) at the printed rational point c0.
Source: Manvir Jaswal, DOI 10.5281/zenodo.23437117,
Proposition 5.1 and its specialization argument. Hensel lifting is proved
by Mathlib's completeness and Henselian-ring theorems.
-/

namespace Z2Z4Rank6.FunctionFieldLocal

open scoped Classical

noncomputable section

open Polynomial

/-- A simple square root of the constant coefficient lifts to a
power-series square root with that prescribed constant term. -/
theorem exists_square_root_with_constant {F : Type*} [Field F] [CharZero F]
    (f : PowerSeries F) (a0 : F)
    (ha : a0^2 = PowerSeries.constantCoeff f) (ha0 : a0 ≠ 0) :
    ∃ a : PowerSeries F, a^2 = f ∧ PowerSeries.constantCoeff a = a0 := by
  let I : Ideal (PowerSeries F) := Ideal.span {PowerSeries.X}
  let g : Polynomial (PowerSeries F) := Polynomial.X^2-Polynomial.C f
  have hg : g.Monic := Polynomial.monic_X_pow_sub_C f (by decide)
  have hroot : g.eval (PowerSeries.C a0) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp [g, ha]
  have hderiv : g.derivative.eval (PowerSeries.C a0) = 2*PowerSeries.C a0 := by
    norm_num [g]
  have hunit : IsUnit (g.derivative.eval (PowerSeries.C a0)) := by
    rw [hderiv, PowerSeries.isUnit_iff_constantCoeff]
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_mul, map_ofNat, PowerSeries.constantCoeff_C] using
      mul_ne_zero (by norm_num : (2 : F) ≠ 0) ha0
  obtain ⟨a, haroot, hamod⟩ := HenselianRing.is_henselian (I := I) g hg
    (PowerSeries.C a0) hroot (hunit.map (Ideal.Quotient.mk I))
  refine ⟨a, ?_, ?_⟩
  · simpa [g, Polynomial.IsRoot, sub_eq_zero] using haroot
  · rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hamod
    simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] using hamod

/-- Formal power series at the rational point c0. -/
abbrev PS := PowerSeries ℚ
/-- Their complete discrete valuation fraction field. -/
abbrev LS := LaurentSeries ℚ

/-- The local parameter map m=m0+T. -/
def mSeries : PS := PowerSeries.C baseC0.m+PowerSeries.X

@[simp] theorem mSeries_constant : PowerSeries.constantCoeff mSeries = baseC0.m := by
  simp [mSeries]

/-- The first formal square root, chosen to have constant term u0. -/
def uSeries : PS := Classical.choose (exists_square_root_with_constant
  (q1 (mSeries^2)) baseC0.u
  (by simpa [q1, map_ofNat] using baseC0.u_sq)
  (by norm_num [baseC0]))

/-- The second formal square root, chosen to have constant term v0. -/
def vSeries : PS := Classical.choose (exists_square_root_with_constant
  (q2 (mSeries^2)) baseC0.v
  (by simpa [q2, map_ofNat] using baseC0.v_sq)
  (by norm_num [baseC0]))

theorem uSeries_spec : uSeries^2 = q1 (mSeries^2) ∧
    PowerSeries.constantCoeff uSeries = baseC0.u :=
  Classical.choose_spec (exists_square_root_with_constant
    (q1 (mSeries^2)) baseC0.u
    (by simpa [q1, map_ofNat] using baseC0.u_sq)
    (by norm_num [baseC0]))

theorem vSeries_spec : vSeries^2 = q2 (mSeries^2) ∧
    PowerSeries.constantCoeff vSeries = baseC0.v :=
  Classical.choose_spec (exists_square_root_with_constant
    (q2 (mSeries^2)) baseC0.v
    (by simpa [q2, map_ofNat] using baseC0.v_sq)
    (by norm_num [baseC0]))

/-- Polynomial substitution m↦m0+T, followed by the injective polynomial to
power-series inclusion. -/
def polynomialSeries : ℚ[X] →+* PS :=
  Polynomial.coeToPowerSeries.ringHom.comp
    (Polynomial.algEquivAevalXAddC baseC0.m).toRingHom

theorem polynomialSeries_injective : Function.Injective polynomialSeries :=
  (Polynomial.coe_injective ℚ).comp (Polynomial.algEquivAevalXAddC baseC0.m).injective

@[simp] theorem polynomialSeries_X : polynomialSeries Polynomial.X = mSeries := by
  simp [polynomialSeries, Polynomial.algEquivAevalXAddC_apply, mSeries, add_comm]

/-- The shifted polynomial embedding into Q((T)). -/
def polynomialLaurent : ℚ[X] →+* LS := (algebraMap PS LS).comp polynomialSeries

theorem polynomialLaurent_injective : Function.Injective polynomialLaurent :=
  (IsFractionRing.injective PS LS).comp polynomialSeries_injective

/-- The shifted field embedding Q(m)→Q((T)). -/
def baseEmbedding : FunctionField.Base →+* LS :=
  IsFractionRing.lift (K := FunctionField.Base) polynomialLaurent_injective

@[simp] theorem baseEmbedding_polynomial (p : ℚ[X]) :
    baseEmbedding (algebraMap ℚ[X] FunctionField.Base p) = polynomialLaurent p :=
  IsFractionRing.lift_algebraMap polynomialLaurent_injective p

@[simp] theorem baseEmbedding_X : baseEmbedding RatFunc.X = algebraMap PS LS mSeries := by
  rw [← RatFunc.algebraMap_X, baseEmbedding_polynomial]
  simp [polynomialLaurent]

/-- The universal root-algebra map written explicitly on its two coefficients.
This formulation allows an arbitrary coefficient ring homomorphism. -/
def quadraticLift {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R) (r : S) (hr : r^2 = f d) :
    QuadraticAlgebra R d 0 →+* S where
  toFun z := f z.re+f z.im*r
  map_zero' := by simp
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      zero_mul, add_zero]
    linear_combination -(f z.im*f w.im)*hr

@[simp] theorem quadraticLift_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R) (r : S) (hr : r^2 = f d) (a : R) :
    quadraticLift f d r hr (algebraMap R (QuadraticAlgebra R d 0) a) = f a := by
  simp [quadraticLift]

@[simp] theorem quadraticLift_omega {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R) (r : S) (hr : r^2 = f d) :
    quadraticLift f d r hr QuadraticAlgebra.omega = r := by
  simp [quadraticLift, QuadraticAlgebra.omega]

private theorem local_u_relation : (algebraMap PS LS uSeries)^2 =
    baseEmbedding FunctionField.d1 := by
  rw [← map_pow, uSeries_spec.1]
  simp [FunctionField.d1, q1, map_ofNat]

/-- The first quadratic field embedding, choosing the root with
constant term u0. -/
def firstEmbedding : FunctionField.First →+* LS :=
  quadraticLift baseEmbedding FunctionField.d1 (algebraMap PS LS uSeries) local_u_relation

private theorem local_v_relation : (algebraMap PS LS vSeries)^2 =
    firstEmbedding FunctionField.d2First := by
  rw [← map_pow, vSeries_spec.1]
  simp [firstEmbedding, FunctionField.d2First, FunctionField.d2, q2, map_ofNat]

/-- The field embedding Q(C)→Q((T)) at the printed point c0. -/
def embedding : FunctionField.K →+* LS :=
  quadraticLift firstEmbedding FunctionField.d2First (algebraMap PS LS vSeries) local_v_relation

theorem embedding_injective : Function.Injective embedding := embedding.injective

@[simp] theorem embedding_base (r : FunctionField.Base) :
    embedding (algebraMap FunctionField.Base FunctionField.K r) = baseEmbedding r := by
  rw [IsScalarTower.algebraMap_apply FunctionField.Base FunctionField.First FunctionField.K]
  simp [embedding, firstEmbedding]

@[simp] theorem embedding_m : embedding FunctionField.m = algebraMap PS LS mSeries := by
  simp [FunctionField.m]

@[simp] theorem embedding_u : embedding FunctionField.u = algebraMap PS LS uSeries := by
  simp [FunctionField.u, embedding, firstEmbedding]

@[simp] theorem embedding_v : embedding FunctionField.v = algebraMap PS LS vSeries := by
  simp [FunctionField.v, embedding]

end
end Z2Z4Rank6.FunctionFieldLocal
