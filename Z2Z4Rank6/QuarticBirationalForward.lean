import Z2Z4Rank6.QuarticBirational

/-!
# The forward half of the pointed-quartic birational formulas

All claims are direct field identities. Together with QuarticBirational they
check both directions on the charts where the displayed denominators do not
vanish.
-/
namespace Z2Z4Rank6
section Field
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem pointed_forward_quadratic (a b c d q t eta : K) (ht : t≠0)
    (hE : eta^2=pointedQuartic a b c d q t) :
    let X := pointedForwardX d q t eta
    pointedInverseDen a q X*t^2-2*pointedInverseLinear b d q X*t+
      (d^2-4*q^2*X-4*c*q^2)=0 := by
  let X := pointedForwardX d q t eta
  change pointedInverseDen a q X*t^2-2*pointedInverseLinear b d q X*t+
    (d^2-4*q^2*X-4*c*q^2)=0
  have hrel : X*t^2-d*t-2*q^2=2*q*eta := by
    dsimp only [X,pointedForwardX]
    field_simp
    ring
  have hz : t^2*(pointedInverseDen a q X*t^2-2*pointedInverseLinear b d q X*t+
      (d^2-4*q^2*X-4*c*q^2))=0 := by
    simp only [pointedInverseDen,pointedInverseLinear,pointedQuartic] at *
    linear_combination (X*t^2-d*t-2*q^2+2*q*eta)*hrel+4*q^2*hE
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 ht)

theorem pointed_forward_equation (a b c d q t eta : K) (hq : q≠0) (ht : t≠0)
    (hE : eta^2=pointedQuartic a b c d q t) :
    (pointedForwardY a b d q t eta)^2=
      pointedCubic a b c d q (pointedForwardX d q t eta) := by
  have hQ := pointed_forward_quadratic a b c d q t eta ht hE
  dsimp only at hQ
  simp only [pointedForwardY]
  generalize hX : pointedForwardX d q t eta=X at *
  field_simp
  simp only [pointedInverseDen,pointedInverseLinear,pointedCubic] at *
  linear_combination (X^2-4*a*q^2)*hQ

theorem pointed_forward_inverse_T (a b d q t eta : K) (hq : q≠0)
    (hA : pointedInverseDen a q (pointedForwardX d q t eta)≠0) :
    pointedInverseT a b d q (pointedForwardX d q t eta)
      (pointedForwardY a b d q t eta)=t := by
  simp only [pointedInverseT,pointedInverseNum,pointedForwardY]
  field_simp
  ring

theorem pointed_forward_inverse_eta (a b d q t eta : K) (hq : q≠0) (ht : t≠0)
    (hA : pointedInverseDen a q (pointedForwardX d q t eta)≠0) :
    pointedInverseEta a b d q (pointedForwardX d q t eta)
      (pointedForwardY a b d q t eta)=eta := by
  unfold pointedInverseEta
  rw [pointed_forward_inverse_T a b d q t eta hq hA]
  unfold pointedForwardX
  field_simp
  ring

end Field
end Z2Z4Rank6
