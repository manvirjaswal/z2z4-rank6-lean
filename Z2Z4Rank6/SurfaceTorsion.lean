import Z2Z4Rank6.FamilyIdentities
import Mathlib.GroupTheory.OrderOfElement

/-!
# The order-four point on the surface Y

The elliptic-point group calculation in Lemma 3.1(a) of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. The point is
`(-w,14w(n²−2n+9801))`, the printed `(-w,w(a−b))` after n=m².
-/

namespace Z2Z4Rank6

section Ring

variable {R : Type*} [CommRing R]

/-- The equation `Y: y²=x(x²+Sx+w²)` from equation (3.1). -/
def surfaceCurve (n : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := surfaceS n
  a₃ := 0
  a₄ := (surfaceW n)^2
  a₆ := 0

theorem surfaceCurve_equation_iff (n x y : R) :
    (surfaceCurve n).toAffine.Equation x y ↔ y^2=x*(x^2+surfaceS n*x+(surfaceW n)^2) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [surfaceCurve, zero_mul, add_zero]
  ring_nf

theorem surfaceCurve_discriminant (n : R) :
    (surfaceCurve n).Δ=16*(surfaceW n)^4*((surfaceS n)^2-4*(surfaceW n)^2) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, surfaceCurve]
  ring

/-- The equation X is exactly the base change n=m² of the printed surface equation. -/
theorem surfaceCurve_base_change (m : R) : surfaceCurve (m^2)=X m := by
  ext <;> simp [surfaceCurve, X, E, surfaceS_base_change, surfaceW_base_change, mul_pow]

theorem surfacePoint_four_equation (n : R) :
    (surfaceCurve n).toAffine.Equation (-surfaceW n) (14*surfaceW n*twistN n) := by
  rw [surfaceCurve_equation_iff]
  have h := surfaceS_sub_twoW n
  calc
    _=(surfaceW n)^2*(surfaceS n-2*surfaceW n) := by rw [h]; ring
    _=_ := by ring

end Ring

section Field

variable {K : Type*} [Field K]

theorem surfaceW_ne_zero_of_elliptic (n : K) [(surfaceCurve n).IsElliptic] : surfaceW n ≠ 0 := by
  intro hw
  apply (surfaceCurve n).isUnit_Δ.ne_zero
  rw [surfaceCurve_discriminant, hw]
  ring

theorem twistN_ne_zero_of_elliptic (n : K) [(surfaceCurve n).IsElliptic] : twistN n ≠ 0 := by
  intro hN
  apply (surfaceCurve n).isUnit_Δ.ne_zero
  rw [surfaceCurve_discriminant, surface_discriminant_factorization, hN]
  ring

/-- The printed order-four point as a Mathlib group element. -/
def surfacePointFour (n : K) [(surfaceCurve n).IsElliptic] : (surfaceCurve n).toAffine.Point :=
  .mk (surfacePoint_four_equation n)

def surfacePointTwo (n : K) [(surfaceCurve n).IsElliptic] : (surfaceCurve n).toAffine.Point :=
  .mk ((surfaceCurve_equation_iff n 0 0).mpr (by ring))

theorem surfacePointTwo_nonzero (n : K) [(surfaceCurve n).IsElliptic] :
    surfacePointTwo n ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

variable [DecidableEq K]

theorem surfacePointTwo_double (n : K) [(surfaceCurve n).IsElliptic] :
    surfacePointTwo n+surfacePointTwo n=0 := by
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [surfaceCurve, WeierstrassCurve.Affine.negY]

variable [CharZero K]

/-- Doubling the printed point gives exactly `(0,0)`, as asserted in Lemma 3.1(a). -/
theorem surfacePointFour_double (n : K) [(surfaceCurve n).IsElliptic] :
    surfacePointFour n+surfacePointFour n=surfacePointTwo n := by
  have hw := surfaceW_ne_zero_of_elliptic n
  have hN := twistN_ne_zero_of_elliptic n
  have hy : 14*surfaceW n*twistN n ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hw) hN
  have hneg : 14*surfaceW n*twistN n ≠
      (surfaceCurve n).toAffine.negY (-surfaceW n) (14*surfaceW n*twistN n) := by
    simp only [WeierstrassCurve.Affine.negY, surfaceCurve, zero_mul, sub_zero]
    intro h
    apply hy
    linear_combination (1/2:K)*h
  change WeierstrassCurve.Affine.Point.some _ _ _ +
    WeierstrassCurve.Affine.Point.some _ _ _ = WeierstrassCurve.Affine.Point.some _ _ _
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
  have hslope : (surfaceCurve n).toAffine.slope (-surfaceW n) (-surfaceW n)
      (14*surfaceW n*twistN n) (14*surfaceW n*twistN n) = -14*twistN n := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
    simp only [surfaceCurve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero]
    field_simp
    unfold surfaceS surfaceW twistN
    ring
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor <;>
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY] <;>
    rw [hslope] <;>
    simp only [WeierstrassCurve.Affine.negY, surfaceCurve] <;>
    unfold surfaceS surfaceW twistN <;> ring

theorem surfacePointFour_quadruple (n : K) [(surfaceCurve n).IsElliptic] :
    (4 : ℕ) • surfacePointFour n=0 := by
  calc
    4 • surfacePointFour n=(surfacePointFour n+surfacePointFour n)+
      (surfacePointFour n+surfacePointFour n) := by abel
    _=0 := by rw [surfacePointFour_double, surfacePointTwo_double]

/-- The point printed in Lemma 3.1(a) has exact additive order four. -/
theorem surfacePointFour_order (n : K) [(surfaceCurve n).IsElliptic] :
    addOrderOf (surfacePointFour n)=4 := by
  have htwo : (2 : ℕ) • surfacePointFour n ≠ 0 := by
    simpa only [two_nsmul, surfacePointFour_double] using surfacePointTwo_nonzero n
  simpa using (addOrderOf_eq_prime_pow (p := 2) (n := 1) htwo (surfacePointFour_quadruple n))

end Field

end Z2Z4Rank6
