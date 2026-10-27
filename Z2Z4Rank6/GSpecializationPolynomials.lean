module

public import Z2Z4Rank6.GTwistSelmerData
public import Z2Z4Rank6.GusicTadicFactorization

@[expose] public section

/-!
# The h-twist polynomial in Proposition 7.2(b)

Exact primitive content and polynomial definitions for Jaswal,
DOI: 10.5281/zenodo.23437117. The h-twist fiber is the one used in
the separate arithmetic certificate module.
-/

namespace Z2Z4Rank6.GSpecialization

open Polynomial
noncomputable section

abbrev hPoly : ℤ[X] := GTwistSelmer.hPolynomial
abbrev parameter : ℚ := GTwistSelmer.parameter

theorem hPoly_content : hPoly.content = 1 := by
  have h2 : hPoly.coeff 2 = -9998 := by norm_num [hPoly,GTwistSelmer.hPolynomial]
  have h4 : hPoly.coeff 4 = 99 := by norm_num [hPoly,GTwistSelmer.hPolynomial]
  have hd2 : hPoly.content ∣ (-9998 : ℤ) := h2 ▸ content_dvd_coeff (p := hPoly) 2
  have hd4 : hPoly.content ∣ (99 : ℤ) := h4 ▸ content_dvd_coeff (p := hPoly) 4
  have hd1 : hPoly.content ∣ 1 := by
    convert dvd_add hd2 (dvd_mul_of_dvd_right hd4 101) using 1; norm_num
  have hn : normalize hPoly.content = 1 := normalize_eq_one.mpr (isUnit_of_dvd_one hd1)
  simpa only [normalize_content] using hn

theorem hPoly_primitive : hPoly.IsPrimitive := isPrimitive_iff_content_eq_one.mpr hPoly_content

theorem hPoly_ne_zero : hPoly ≠ 0 := by
  intro h
  have hh := congrArg (fun f : ℤ[X] => f.coeff 4) h
  norm_num [hPoly,GTwistSelmer.hPolynomial] at hh

end
end Z2Z4Rank6.GSpecialization
