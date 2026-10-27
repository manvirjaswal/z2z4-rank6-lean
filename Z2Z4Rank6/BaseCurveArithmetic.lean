import Z2Z4Rank6.Basic
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The infinite-order point on E_C

Point arithmetic from the proof of Lemma 4.1(b) in M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. Every coordinate calculation uses
Mathlib's Weierstrass point group.
-/

namespace Z2Z4Rank6

theorem ec_discriminant : EC.Δ = (119563310477318400 : ℚ) := by
  norm_num [EC, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance ec_isElliptic : EC.IsElliptic where
  isUnit := by rw [isUnit_iff_ne_zero, ec_discriminant]; norm_num

theorem ec_equation_iff (x y : ℚ) :
    EC.toAffine.Equation x y ↔ y^2 = x^3 + x^2 - 137620*x - 10504000 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [EC]
  ring_nf

def ecP : RationalPoints EC :=
  .mk ((ec_equation_iff (-322) 726).mpr (by norm_num))

def ecTriple : RationalPoints EC :=
  .mk ((ec_equation_iff (-1901193922 / 2521^2) (31980410728794 / 2521^3)).mpr
    (by norm_num))

theorem ecP_triple : (3 : ℕ) • ecP = ecTriple := by
  norm_num [ecP, ecTriple, WeierstrassCurve.Affine.Point.mk,
    three_nsmul, WeierstrassCurve.Affine.Point.add_def,
    WeierstrassCurve.Affine.Point.add, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, EC]

theorem ecTriple_x_den : (-1901193922 / 2521^2 : ℚ).den = 2521^2 := by norm_num

theorem ecTriple_x_nonintegral :
    2521 ∣ (-1901193922 / 2521^2 : ℚ).den := by norm_num

/-- An equation has integral coefficients, without any minimality condition. -/
def IntegralWeierstrass (W : WeierstrassCurve ℚ) : Prop :=
  ∃ W₀ : WeierstrassCurve ℤ, W₀.map (Int.castRingHom ℚ) = W

/-- The rational, odd-prime specialization of Cassels' denominator theorem:
Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed. (2009), Theorem VII.3.4,
p. 193. The printed theorem allows nonminimal integral equations. For `K=ℚ_p`
and odd `p`, its bound `floor(1/(p^n-p^(n-1)))` is zero; together with part (a),
this says every finite-order affine point has p-integral coordinates.
 -/
def OddPrimeTorsionIntegrality : Prop :=
  ∀ (W : WeierstrassCurve ℚ), W.IsElliptic → IntegralWeierstrass W →
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
      ∀ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x y h) → ¬ p ∣ x.den

theorem ec_integral : IntegralWeierstrass EC := by
  refine ⟨⟨0,1,0,-137620,-10504000⟩, ?_⟩
  ext <;> norm_num [WeierstrassCurve.map, EC]

/-- Under the denominator theorem, the point printed in
Lemma 4.1(b) has infinite order in the E_C rational point group. -/
theorem ecP_infinite_order (hSilvermanVII34 : OddPrimeTorsionIntegrality) :
    ¬ IsOfFinAddOrder ecP := by
  intro hP
  have h3 : IsOfFinAddOrder ecTriple := ecP_triple ▸ hP.nsmul
  exact (hSilvermanVII34 EC inferInstance ec_integral 2521 (by norm_num)
    (by norm_num) _ _ _ h3) ecTriple_x_nonintegral

theorem ec_infinite (hSilvermanVII34 : OddPrimeTorsionIntegrality) :
    Infinite (RationalPoints EC) :=
  Infinite.of_injective (fun n : ℕ => n • ecP)
    (injective_nsmul_iff_not_isOfFinAddOrder.mpr (ecP_infinite_order hSilvermanVII34))

end Z2Z4Rank6
