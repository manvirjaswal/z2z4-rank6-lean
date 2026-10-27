import Z2Z4Rank6.Basic
import Z2Z4Rank6.TorsionGroups
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Torsion on the split family

The explicit group calculations used in Lemma 6.1 of Manvir Jaswal,
"Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six",
DOI: 10.5281/zenodo.23437117.

The square obstruction to halving is obtained from the usual duplication
formula, the first component of the descent map used in the printed proof.
-/

namespace Z2Z4Rank6

open WeierstrassCurve Affine Affine.Point

theorem E_equation_iff (α β x y : ℚ) :
    (E α β).toAffine.Equation x y ↔ y ^ 2 = x * (x + α ^ 2) * (x + β ^ 2) := by
  rw [Affine.equation_iff]
  simp only [E, zero_mul, add_zero]
  constructor <;> intro h <;> nlinarith [h]

theorem E_discriminant (α β : ℚ) :
    (E α β).Δ = 16 * α ^ 4 * β ^ 4 * (α ^ 2 - β ^ 2) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, E]
  ring

theorem E_good (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) : GoodCurve (E α β) := by
  have ha : α ≠ 0 := by aesop
  have hb : β ≠ 0 := by aesop
  have hab : α ^ 2 - β ^ 2 ≠ 0 := by aesop
  constructor
  rw [isUnit_iff_ne_zero, E_discriminant]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha))
    (pow_ne_zero _ hb)) (pow_ne_zero _ hab)

private theorem E_nonsingular (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0)
    (x y : ℚ) (heq : y ^ 2 = x * (x + α ^ 2) * (x + β ^ 2)) :
    (E α β).toAffine.Nonsingular x y := by
  let _ := E_good α β h
  exact Affine.equation_iff_nonsingular.mp ((E_equation_iff α β x y).mpr heq)

/-- The two-torsion point `(0,0)` on `E_{a,b}`. -/
def twoZero (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) : RationalPoints (E α β) :=
  .some 0 0 (E_nonsingular α β h 0 0 (by ring))

/-- The independent two-torsion point `(-a²,0)` on `E_{a,b}`. -/
def twoLeft (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) : RationalPoints (E α β) :=
  .some (-(α ^ 2)) 0 (E_nonsingular α β h _ 0 (by ring))

/-- The printed four-torsion point `(ab,ab(a+b))` on `E_{a,b}`. -/
def fourPoint (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) : RationalPoints (E α β) :=
  .some (α * β) (α * β * (α + β)) (E_nonsingular α β h _ _ (by ring))

theorem twoZero_ne_zero (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    twoZero α β h ≠ 0 := Affine.Point.some_ne_zero _

theorem twoLeft_ne_zero (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    twoLeft α β h ≠ 0 := Affine.Point.some_ne_zero _

theorem twoLeft_ne_twoZero (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    twoLeft α β h ≠ twoZero α β h := by
  intro heq
  have hx := (Affine.Point.some.inj heq).1
  have hα : α ≠ 0 := by aesop
  exact hα (sq_eq_zero_iff.mp (by linarith))

theorem twoZero_double (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    twoZero α β h + twoZero α β h = 0 := by
  apply Affine.Point.add_self_of_Y_eq
  norm_num [Affine.negY, E]

theorem twoLeft_double (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    twoLeft α β h + twoLeft α β h = 0 := by
  apply Affine.Point.add_self_of_Y_eq
  norm_num [Affine.negY, E]

theorem fourPoint_double (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    fourPoint α β h + fourPoint α β h = twoZero α β h := by
  have hα : α ≠ 0 := by aesop
  have hβ : β ≠ 0 := by aesop
  have hsum : α + β ≠ 0 := by
    intro hz
    have hdiff : α ^ 2 - β ^ 2 = 0 := by
      have heq : α = -β := by linarith
      rw [heq]
      ring
    exact h (by rw [hdiff, mul_zero])
  have hy : α * β * (α + β) ≠ 0 := mul_ne_zero (mul_ne_zero hα hβ) hsum
  have hneg : α * β * (α + β) ≠ (E α β).toAffine.negY (α * β) (α * β * (α + β)) := by
    simpa only [Affine.negY, E, zero_mul, sub_zero] using
      (show α * β * (α + β) ≠ -(α * β * (α + β)) by intro heq; apply hy; linarith)
  change Affine.Point.some _ _ _ + Affine.Point.some _ _ _ = Affine.Point.some _ _ _
  rw [Affine.Point.add_self_of_Y_ne hneg]
  have hslope : (E α β).toAffine.slope (α * β) (α * β) (α * β * (α + β))
      (α * β * (α + β)) = α + β := by
    rw [Affine.slope_of_Y_ne rfl hneg]
    simp only [E, Affine.negY, zero_mul, sub_zero]
    field_simp
    ring
  simp only [Affine.Point.some.injEq]
  constructor <;> simp only [Affine.addX, Affine.addY, Affine.negAddY] <;>
    rw [hslope] <;> simp only [Affine.negY, E] <;> ring

theorem fourPoint_quadruple (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    (4 : ℕ) • fourPoint α β h = 0 := by
  calc
    4 • fourPoint α β h = (fourPoint α β h + fourPoint α β h) +
        (fourPoint α β h + fourPoint α β h) := by abel
    _ = 0 := by rw [fourPoint_double, twoZero_double]

/-- Every nonsingular curve of the printed split form has a subgroup
isomorphic to `Z/2 × Z/4`, with the displayed two generators. -/
theorem E_two_four_inclusion (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    ∃ f : (ZMod 2 × ZMod 4) →+ RationalPoints (E α β), Function.Injective f := by
  apply two_four_injective (twoLeft α β h) (fourPoint α β h)
  · simpa only [two_nsmul] using twoLeft_double α β h
  · exact fourPoint_quadruple α β h
  · exact twoLeft_ne_zero α β h
  · simpa only [two_nsmul, fourPoint_double] using twoZero_ne_zero α β h
  · simpa only [two_nsmul, fourPoint_double] using twoLeft_ne_twoZero α β h

theorem E_torsion_two_four_inclusion (α β : ℚ) (h : α * β * (α ^ 2 - β ^ 2) ≠ 0) :
    ∃ f : (ZMod 2 × ZMod 4) →+ AddCommGroup.torsion (RationalPoints (E α β)),
      Function.Injective f := by
  obtain ⟨f, hf⟩ := E_two_four_inclusion α β h
  let f' := f.codRestrict (AddCommGroup.torsion (RationalPoints (E α β))) (fun x =>
    f.isOfFinAddOrder (isOfFinAddOrder_of_finite x))
  refine ⟨f', ?_⟩
  intro x y hxy
  apply hf
  exact congrArg Subtype.val hxy

/-- The affine x-coordinate of a nonzero double is a rational square. -/
theorem E_double_x (α β x y : ℚ)
    (h : (E α β).toAffine.Equation x y) (hy : y ≠ 0) :
    (E α β).toAffine.addX x x ((E α β).toAffine.slope x x y y) =
      ((x ^ 2 - α ^ 2 * β ^ 2) / (2 * y)) ^ 2 := by
  have hn : y ≠ (E α β).toAffine.negY x y := by
    simpa only [Affine.negY, E, zero_mul, sub_zero] using
      (show y ≠ -y by intro hneg; apply hy; linarith)
  rw [Affine.slope_of_Y_ne rfl hn]
  simp only [Affine.addX, Affine.negY, E, zero_mul, sub_zero, add_zero]
  rw [show y - -y = 2 * y by ring]
  rw [E_equation_iff] at h
  field_simp
  linear_combination -(8 * x + 4 * (α ^ 2 + β ^ 2)) * h

/-- The first-component halving obstruction used in Lemma 6.1. -/
theorem E_double_isSquare (α β : ℚ) (P : RationalPoints (E α β)) (hP : P + P ≠ 0) :
    ∃ (x y : ℚ) (hxy : (E α β).toAffine.Nonsingular x y),
      P + P = Affine.Point.some x y hxy ∧ IsSquare x := by
  cases P with
  | zero => exact (hP rfl).elim
  | @some x y h =>
      have hy : y ≠ 0 := by
        intro hy
        apply hP
        apply Affine.Point.add_self_of_Y_eq
        simp only [Affine.negY, E, zero_mul, sub_zero, hy, _root_.neg_zero]
      have hn : y ≠ (E α β).toAffine.negY x y := by
        simpa only [Affine.negY, E, zero_mul, sub_zero] using
          (show y ≠ -y by intro hneg; apply hy; linarith)
      refine ⟨_, _, _, Affine.Point.add_self_of_Y_ne hn, ?_⟩
      rw [E_double_x α β x y h.1 hy]
      exact ⟨_, pow_two _⟩

/-- The three possible nonidentity points of order two, in coordinates. -/
theorem E_two_torsion_x (α β x y : ℚ) (hxy : (E α β).toAffine.Nonsingular x y)
    (hP : Affine.Point.some x y hxy + Affine.Point.some x y hxy = 0) :
    y = 0 ∧ (x = 0 ∨ x = -(α ^ 2) ∨ x = -(β ^ 2)) := by
  have hyneg : y = (E α β).toAffine.negY x y := by
    by_contra hn
    rw [Affine.Point.add_self_of_Y_ne hn] at hP
    exact Affine.Point.some_ne_zero _ hP
  have hy : y = 0 := by
    simp only [Affine.negY, E, zero_mul, sub_zero] at hyneg
    linarith
  have heq := (E_equation_iff α β x y).mp hxy.1
  have hmul : x * (x + α ^ 2) * (x + β ^ 2) = 0 := by rw [← heq, hy]; norm_num
  refine ⟨hy, ?_⟩
  rcases mul_eq_zero.mp hmul with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

private theorem neg_sq_not_isSquare (z : ℚ) (hz : z ≠ 0) : ¬IsSquare (-(z ^ 2)) := by
  rintro ⟨r, hr⟩
  nlinarith [sq_pos_of_ne_zero hz, sq_nonneg r]

/-- Nonsquare `ab` and `−ab` prevent rational points of order eight.
This is the halving argument in the proof of Lemma 6.1. -/
theorem E_no_order_eight (α β : ℚ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hp : ¬IsSquare (α * β)) (hn : ¬IsSquare (-(α * β))) :
    ¬∃ P : RationalPoints (E α β), addOrderOf P = 8 := by
  rintro ⟨P, hP⟩
  have h8 : (8 : ℕ) • P = 0 := (addOrderOf_dvd_iff_nsmul_eq_zero).mp (by rw [hP])
  have h4 : (4 : ℕ) • P ≠ 0 := by
    intro hz
    have hh := (addOrderOf_dvd_iff_nsmul_eq_zero).mpr hz
    rw [hP] at hh
    norm_num at hh
  have h2 : P + P ≠ 0 := by
    intro h
    apply h4
    simp only [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul, two_nsmul, h, add_zero]
  obtain ⟨x, y, hxy, heq, hsq⟩ := E_double_isSquare α β P h2
  have hQ2 : Affine.Point.some x y hxy + Affine.Point.some x y hxy ≠ 0 := by
    rw [← heq]
    simpa only [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul, two_nsmul] using h4
  obtain ⟨r, s, hrs, hrseq, hrsq⟩ := E_double_isSquare α β (.some x y hxy) hQ2
  have hR2 : Affine.Point.some r s hrs + Affine.Point.some r s hrs = 0 := by
    rw [← hrseq, ← heq]
    simpa only [show (8 : ℕ) = 2 * (2 * 2) by decide, mul_nsmul, two_nsmul] using h8
  have hroots := (E_two_torsion_x α β r s hrs hR2).2
  have hr : r = 0 := by
    rcases hroots with hr | hr | hr
    · exact hr
    · exact (neg_sq_not_isSquare α hα (hr ▸ hrsq)).elim
    · exact (neg_sq_not_isSquare β hβ (hr ▸ hrsq)).elim
  have hy : y ≠ 0 := by
    intro hy
    apply hQ2
    apply Affine.Point.add_self_of_Y_eq
    simp only [Affine.negY, E, zero_mul, sub_zero, hy, _root_.neg_zero]
  have hneg : y ≠ (E α β).toAffine.negY x y := by
    simpa only [Affine.negY, E, zero_mul, sub_zero] using
      (show y ≠ -y by intro heq; apply hy; linarith)
  rw [Affine.Point.add_self_of_Y_ne hneg] at hrseq
  have hxdouble := (Affine.Point.some.inj hrseq).1
  rw [E_double_x α β x y hxy.1 hy, hr] at hxdouble
  have hxprod : x ^ 2 = α ^ 2 * β ^ 2 := by
    have hzero := (sq_eq_zero_iff.mp hxdouble)
    exact sub_eq_zero.mp ((div_eq_zero_iff).mp hzero |>.resolve_right (mul_ne_zero (by norm_num) hy))
  have hx : x = α * β ∨ x = -(α * β) := by
    apply (sq_eq_sq_iff_eq_or_eq_neg).mp
    simpa only [mul_pow] using hxprod
  rcases hx with hx | hx
  · exact hp (hx ▸ hsq)
  · exact hn (hx ▸ hsq)

/-- Lemma 6.1: nonsquare `ab` and `−ab` give torsion exactly
`Z/2 × Z/4`. The hypothesis is Mazur's classification, stated for every rational elliptic curve
in `MazurTorsionTheorem`. -/
theorem E_torsion_exact (hMazur : MazurTorsionTheorem) (α β : ℚ)
    (h : α * β * (α ^ 2 - β ^ 2) ≠ 0)
    (hp : ¬IsSquare (α * β)) (hn : ¬IsSquare (-(α * β))) : TorsionExact (E α β) := by
  obtain ⟨f, hf⟩ := E_torsion_two_four_inclusion α β h
  apply two_four_equiv_of_mazur (hMazur (E α β) (E_good α β h)) f hf
  rintro ⟨Q, hQ⟩
  have hα : α ≠ 0 := by aesop
  have hβ : β ≠ 0 := by aesop
  apply E_no_order_eight α β hα hβ hp hn
  refine ⟨Q.val, ?_⟩
  exact (addOrderOf_injective (AddCommGroup.torsion (RationalPoints (E α β))).subtype
    Subtype.coe_injective Q).trans hQ

end Z2Z4Rank6
