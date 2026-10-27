module

public import Z2Z4Rank6.FunctionField
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Base squareclasses after arbitrary characteristic-zero constant extension

Jaswal, DOI 10.5281/zenodo.23437117, equations (1.3), Lemma 4.1(a).
The two defining radicands and their product stay nonsquare over k(m) for
every characteristic-zero field k. Explicit derivative Bezout identities
prove squarefreeness; integral closedness passes a putative rational-function
square root back to k[m]. These statements concern the polynomials,
not a geometric-integrality predicate for a scheme.
-/
namespace Z2Z4Rank6.GeometricBaseSquareClasses
noncomputable section
open Polynomial
variable (k:Type*) [Field k] [CharZero k]

def firstPolynomial : k[X] := C 15*Polynomial.X^2+C 1210
def secondPolynomial : k[X] := C 10*Polynomial.X^2+C 1215

theorem first_separable : (firstPolynomial k).Separable := by
  rw [Polynomial.separable_def]
  refine ⟨C (1/1210),-(C (1/2420)*Polynomial.X),?_⟩
  norm_num [firstPolynomial,derivative_add,derivative_mul,derivative_pow]
  ring_nf
  norm_num [←C_mul,←C_add]

theorem second_separable : (secondPolynomial k).Separable := by
  rw [Polynomial.separable_def]
  refine ⟨C (1/1215),-(C (1/2430)*Polynomial.X),?_⟩
  norm_num [secondPolynomial,derivative_add,derivative_mul,derivative_pow]
  ring_nf
  norm_num [←C_mul,←C_add]

theorem first_second_coprime : IsCoprime (firstPolynomial k) (secondPolynomial k) := by
  refine ⟨C (-2/1225),C (3/1225),?_⟩
  norm_num [firstPolynomial,secondPolynomial]
  ring_nf
  norm_num [←C_mul,←C_add]
  have h : -C (484/245:k)+C (729/245:k)=1 := by
    rw [←map_neg,←map_add]
    norm_num
  linear_combination h

theorem first_squarefree : Squarefree (firstPolynomial k) := (first_separable k).squarefree
theorem second_squarefree : Squarefree (secondPolynomial k) := (second_separable k).squarefree
theorem product_squarefree : Squarefree (firstPolynomial k*secondPolynomial k) :=
  squarefree_mul_iff.mpr ⟨(first_second_coprime k).isRelPrime,first_squarefree k,second_squarefree k⟩

theorem first_natDegree : (firstPolynomial k).natDegree=2 := by
  unfold firstPolynomial
  compute_degree!
theorem second_natDegree : (secondPolynomial k).natDegree=2 := by
  unfold secondPolynomial
  compute_degree!
theorem product_natDegree : (firstPolynomial k*secondPolynomial k).natDegree=4 := by
  rw [natDegree_mul (first_squarefree k).ne_zero (second_squarefree k).ne_zero,
    first_natDegree,second_natDegree]

omit [CharZero k] in
/-- A nonconstant squarefree polynomial stays nonsquare in its rational-function field. -/
theorem not_isSquare_fraction_of_squarefree (p:k[X]) (hp:Squarefree p)
    (hdeg:0<p.natDegree) : ¬IsSquare (algebraMap k[X] (RatFunc k) p) := by
  rintro ⟨z,hz⟩
  have hint : IsIntegral k[X] (z^2) := by
    rw [sq,←hz]
    exact isIntegral_algebraMap
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R:=k[X]) (by decide:0<(2:ℕ)) hint
  have heq : p=r*r := by
    apply RatFunc.algebraMap_injective k
    simpa only [map_mul,hr] using hz
  have hsq : IsSquare (p*1) := by rw [mul_one]; exact ⟨r,heq⟩
  have hu : IsUnit p := isUnit_of_dvd_one (hp.dvd_of_isSquare_mul hsq)
  exact (Nat.ne_of_gt hdeg) (natDegree_eq_zero_of_isUnit hu)

theorem first_fraction_nonsquare :
    ¬IsSquare (algebraMap k[X] (RatFunc k) (firstPolynomial k)) :=
  not_isSquare_fraction_of_squarefree k _ (first_squarefree k) (by rw [first_natDegree];decide)
theorem second_fraction_nonsquare :
    ¬IsSquare (algebraMap k[X] (RatFunc k) (secondPolynomial k)) :=
  not_isSquare_fraction_of_squarefree k _ (second_squarefree k) (by rw [second_natDegree];decide)
theorem product_fraction_nonsquare :
    ¬IsSquare (algebraMap k[X] (RatFunc k) (firstPolynomial k*secondPolynomial k)) :=
  not_isSquare_fraction_of_squarefree k _ (product_squarefree k) (by rw [product_natDegree];decide)

/-- The rational-function radicands over the extended constants. -/
def d1 : RatFunc k := algebraMap k[X] (RatFunc k) (firstPolynomial k)
def d2 : RatFunc k := algebraMap k[X] (RatFunc k) (secondPolynomial k)

instance first_nonsquare : Fact (¬IsSquare (d1 k)) := ⟨first_fraction_nonsquare k⟩
abbrev First := QuadraticAlgebra (RatFunc k) (d1 k) 0
def d2First : First k := algebraMap (RatFunc k) (First k) (d2 k)

theorem d2First_nonsquare : ¬IsSquare (d2First k) := by
  apply FunctionField.not_isSquare_in_quadratic
  · exact second_fraction_nonsquare k
  · simpa only [d1,d2,←map_mul] using product_fraction_nonsquare k

instance second_nonsquare : Fact (¬IsSquare (d2First k)) := ⟨d2First_nonsquare k⟩

/-- The quadratic tower stays a degree-four field after every
characteristic-zero extension of the constants. -/
abbrev K := QuadraticAlgebra (First k) (d2First k) 0

omit [CharZero k] in
theorem finrank_eq_four : Module.finrank (RatFunc k) (K k)=4 := by
  rw [←Module.finrank_mul_finrank (RatFunc k) (First k) (K k),
    QuadraticAlgebra.finrank_eq_two,QuadraticAlgebra.finrank_eq_two]

end
end Z2Z4Rank6.GeometricBaseSquareClasses
