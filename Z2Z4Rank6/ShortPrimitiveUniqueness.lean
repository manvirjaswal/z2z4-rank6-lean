import Z2Z4Rank6.ShortNormalization
import Mathlib.RingTheory.Int.Basic

/-!
# Uniqueness of primitive short coefficients under rational scaling

A rational denominator surviving in a fourth/sixth coefficient scale would
supply a prime fourth/sixth common divisor of the primitive target pair.
Applying this to the scale and its inverse forces the scale to be 1 or −1.
This checks the well-defined normalization in the height convention of
Jaswal, DOI 10.5281/zenodo.23437117, Remark 6.3 (height).
-/
namespace Z2Z4Rank6.ShortHeight
noncomputable section
open scoped Classical

private theorem denominator_dvd (q : ℚ) (a b : ℤ) (h : (a:ℚ)=q*(b:ℚ)) :
    (q.den:ℤ)∣b := by
  have hq : (q.den:ℚ)*q=(q.num:ℚ) := by simpa only [mul_comm] using Rat.mul_den_eq_num q
  have heQ : (q.den:ℚ)*(a:ℚ)=(q.num:ℚ)*(b:ℚ) := by
    rw [h,←mul_assoc,hq]
  have he : (q.den:ℤ)*a=q.num*b := by exact_mod_cast heQ
  have hcop : IsCoprime q.num (q.den:ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using q.reduced
  exact hcop.symm.dvd_of_dvd_mul_left ⟨a,he.symm⟩

/-- A rational scale producing integral coefficients from a primitive pair
has denominator one. -/
theorem denominator_eq_one_of_primitive_scale (u : ℚ) (A B A0 B0 : ℤ)
    (hA : (A:ℚ)=u^4*(A0:ℚ)) (hB : (B:ℚ)=u^6*(B0:ℚ))
    (hp : ShortPrimitive A0 B0) : u.den=1 := by
  have hd4 : (u.den:ℤ)^4∣A0 := by
    simpa only [Rat.den_pow,Nat.cast_pow] using denominator_dvd (u^4) A A0 hA
  have hd6 : (u.den:ℤ)^6∣B0 := by
    simpa only [Rat.den_pow,Nat.cast_pow] using denominator_dvd (u^6) B B0 hB
  by_contra hn
  obtain ⟨p,hprime,hpd⟩ := Nat.exists_prime_and_dvd hn
  have hd : (p:ℤ)∣(u.den:ℤ) := by exact_mod_cast hpd
  exact hp p hprime ⟨(pow_dvd_pow_of_dvd hd 4).trans hd4,(pow_dvd_pow_of_dvd hd 6).trans hd6⟩

/-- Primitive integer short pairs can differ by rational scaling only
with scale 1 or −1. -/
theorem rational_scale_eq_one_or_neg_one (u : ℚ) (hu : u≠0) (A B A0 B0 : ℤ)
    (hA : (A:ℚ)=u^4*(A0:ℚ)) (hB : (B:ℚ)=u^6*(B0:ℚ))
    (hp : ShortPrimitive A B) (hp0 : ShortPrimitive A0 B0) : u=1∨u= -1 := by
  have hd := denominator_eq_one_of_primitive_scale u A B A0 B0 hA hB hp0
  have hAi : (A0:ℚ)=(u⁻¹)^4*(A:ℚ) := by rw [hA]; field_simp [hu]
  have hBi : (B0:ℚ)=(u⁻¹)^6*(B:ℚ) := by rw [hB]; field_simp [hu]
  have hdi := denominator_eq_one_of_primitive_scale u⁻¹ A0 B0 A B hAi hBi hp
  have hnum : u=(u.num:ℚ) := by
    conv_lhs => rw [←Rat.num_div_den u,hd]
    simp
  have hnumi : u⁻¹=((u⁻¹).num:ℚ) := by
    conv_lhs => rw [←Rat.num_div_den (u⁻¹),hdi]
    simp
  have hprodQ : (u.num:ℚ)*((u⁻¹).num:ℚ)=1 := by rw [←hnum,←hnumi,mul_inv_cancel₀ hu]
  have hprod : u.num*(u⁻¹).num=1 := by exact_mod_cast hprodQ
  have hunit : IsUnit u.num := isUnit_iff_dvd_one.mpr ⟨(u⁻¹).num,hprod.symm⟩
  rcases Int.isUnit_iff.mp hunit with h1 | hm1
  · left;simpa only [h1,Int.cast_one] using hnum
  · right;simpa only [hm1,Int.cast_neg,Int.cast_one] using hnum

theorem primitive_coefficients_eq_of_rational_scale (u : ℚ) (hu : u≠0)
    (A B A0 B0 : ℤ) (hA : (A:ℚ)=u^4*(A0:ℚ)) (hB : (B:ℚ)=u^6*(B0:ℚ))
    (hp : ShortPrimitive A B) (hp0 : ShortPrimitive A0 B0) : A=A0∧B=B0 := by
  rcases rational_scale_eq_one_or_neg_one u hu A B A0 B0 hA hB hp hp0 with h1 | hm1
  · simp only [h1,one_pow,one_mul] at hA hB
    exact ⟨by exact_mod_cast hA,by exact_mod_cast hB⟩
  · norm_num [hm1] at hA hB
    exact ⟨by exact_mod_cast hA,by exact_mod_cast hB⟩

/-- Any two primitive normalizations of the same raw integer pair have
the same primitive coefficients, hence the same normalized height. -/
theorem Normalization.coefficients_unique {A B : ℤ} (n n' : Normalization A B) :
    n.shortA=n'.shortA∧n.shortB=n'.shortB := by
  let u : ℚ := (n'.scale:ℚ)/(n.scale:ℚ)
  have hd : (n.scale:ℚ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt n.scale_pos)
  have hd' : (n'.scale:ℚ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt n'.scale_pos)
  have hu : u≠0 := div_ne_zero hd' hd
  have hAZ : (n.scale:ℤ)^4*n.shortA=(n'.scale:ℤ)^4*n'.shortA := n.eqA.symm.trans n'.eqA
  have hBZ : (n.scale:ℤ)^6*n.shortB=(n'.scale:ℤ)^6*n'.shortB := n.eqB.symm.trans n'.eqB
  have hAQ : (n.scale:ℚ)^4*(n.shortA:ℚ)=(n'.scale:ℚ)^4*(n'.shortA:ℚ) := by exact_mod_cast hAZ
  have hBQ : (n.scale:ℚ)^6*(n.shortB:ℚ)=(n'.scale:ℚ)^6*(n'.shortB:ℚ) := by exact_mod_cast hBZ
  have hA : (n.shortA:ℚ)=u^4*(n'.shortA:ℚ) := by
    dsimp [u]
    field_simp [hd]
    linear_combination hAQ
  have hB : (n.shortB:ℚ)=u^6*(n'.shortB:ℚ) := by
    dsimp [u]
    field_simp [hd]
    linear_combination hBQ
  exact primitive_coefficients_eq_of_rational_scale u hu _ _ _ _ hA hB n.primitive n'.primitive

theorem Normalization.height_unique {A B : ℤ} (n n' : Normalization A B) : n.height=n'.height := by
  have h := n.coefficients_unique n'
  simp only [Normalization.height,h.1,h.2]

/-- The normalized height is independent of the positive-scale witness. -/
def normalizedHeight (A B : ℤ) (hn : A≠0∨B≠0) : ℕ := (normalization A B hn).height

theorem Normalization.height_eq_normalizedHeight {A B : ℤ} (n : Normalization A B)
    (hn : A≠0∨B≠0) : n.height=normalizedHeight A B hn :=
  n.height_unique (normalization A B hn)

end
end Z2Z4Rank6.ShortHeight
