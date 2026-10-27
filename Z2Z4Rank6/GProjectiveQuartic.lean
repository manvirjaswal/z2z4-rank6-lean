module

public import Common.Elliptic.GenusOneModelTheorem
public import Z2Z4Rank6.GQuarticGeometry

@[expose] public section

/-!
# The complete quartic G is a genus-one curve

Jaswal, Proposition 7.2(a), DOI 10.5281/zenodo.23437117. The scheme is
the weighted Proj of η²=99m⁴−9998m²z²+970299z⁴, with coordinate
weights (m,z,η)=(1,1,2). Its genus follows from the published
Cremona–Fisher–Stoll Theorem 2.8(ii), arXiv:0908.1741v1, p. 6, after
the discriminant computation.
The rational point and Jacobian identification are separate below/files.
-/

namespace Z2Z4Rank6.GProjectiveQuartic
noncomputable section
open AlgebraicGeometry RationalCurveGenus
open BinaryQuarticModel

def model : BinaryQuartic ℚ := ⟨99,0,-9998,0,970299⟩
abbrev scheme := BinaryQuarticModel.scheme model
abbrev structureMap := BinaryQuarticModel.structureMap model

theorem polynomial_eq : polynomial model = gQuarticPolynomial := by
  simp [polynomial,model,gQuarticPolynomial]
  norm_num only [map_ofNat]
  ring

theorem invariant_I : invariantI model = 1252675216 := by
  norm_num [invariantI,model]
theorem invariant_J : invariantJ model = -67150279897472 := by
  norm_num [invariantJ,model]

/-- CFS's model discriminant is sixteen times the ordinary quartic
discriminant printed in the paper. -/
theorem discriminant_eq : discriminant model = 2^22*3^8*5^4*7^8*11^4*37^2 := by
  norm_num [discriminant,c4,c6,invariantI,invariantJ,model]
theorem discriminant_ne_zero : discriminant model ≠ 0 := by
  rw [discriminant_eq]
  norm_num

theorem genus_one (h : GenusOneModelTheorem.CFSTheorem28iiDegreeTwo) :
    IsSmoothProperGenusOne scheme structureMap :=
  GenusOneModelTheorem.binaryQuartic_genus_one h model discriminant_ne_zero

theorem relation_eq : BinaryQuarticModel.relation model =
    MvPolynomial.X 2^2-99*MvPolynomial.X 0^4+
      9998*(MvPolynomial.X 0^2*MvPolynomial.X 1^2)-970299*MvPolynomial.X 1^4 := by
  simp only [BinaryQuarticModel.relation,form,model,map_ofNat,map_neg,map_zero,zero_mul,add_zero]
  ring

end
end Z2Z4Rank6.GProjectiveQuartic
