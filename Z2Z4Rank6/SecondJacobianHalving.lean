import Z2Z4Rank6.SecondJacobianBasic
/-! Elementary second-coordinate halving obstruction for the second Jacobian.
The basic nonsquare-ab torsion criterion is inapplicable here because both
split parameters are squares. -/
namespace Z2Z4Rank6
open WeierstrassCurve Affine Affine.Point

private theorem neg_sq_not_isSquare (z:ℚ)(hz:z≠0):¬IsSquare (-(z^2)) := by
  rintro ⟨r,hr⟩
  nlinarith [sq_pos_of_ne_zero hz,sq_nonneg r]

theorem secondJacobian_double_shift_formula (α β x y:ℚ)
    (h:(E α β).toAffine.Equation x y)(hy:y≠0):
    (E α β).toAffine.addX x x ((E α β).toAffine.slope x x y y)+α^2=
      ((x^2+2*α^2*x+α^2*β^2)/(2*y))^2 := by
  rw [E_double_x α β x y h hy]
  rw [E_equation_iff] at h
  field_simp
  linear_combination 4*α^2*h

theorem secondJacobian_double_shift_isSquare (α β:ℚ)(P:RationalPoints (E α β))
    (hP:P+P≠0)(x y:ℚ)(hxy:(E α β).toAffine.Nonsingular x y)
    (heq:P+P=Point.some x y hxy):IsSquare (x+α^2) := by
  cases P with
  | zero => exact (hP rfl).elim
  | some u v h =>
    have hv:v≠0 := by
      intro hv
      apply hP
      apply Point.add_self_of_Y_eq
      simp only [Affine.negY,E,zero_mul,sub_zero,hv,_root_.neg_zero]
    have hn:v≠(E α β).toAffine.negY u v := by
      simpa only [Affine.negY,E,zero_mul,sub_zero] using
        (show v≠-v by intro hh;apply hv;linarith)
    rw [Point.add_self_of_Y_ne hn] at heq
    have hx := (Point.some.inj heq).1
    rw [←hx,secondJacobian_double_shift_formula α β u v h.1 hv]
    exact ⟨_,pow_two _⟩

theorem secondJacobian_no_order_eight_of_shift (α β : ℚ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hp : ¬IsSquare (α * β+α^2)) (hn : ¬IsSquare (-(α * β))) :
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
  have hshift:IsSquare (x+α^2) := secondJacobian_double_shift_isSquare α β P h2 x y hxy heq
  rcases hx with hx | hx
  · exact hp (hx ▸ hshift)
  · exact hn (hx ▸ hsq)


end Z2Z4Rank6
