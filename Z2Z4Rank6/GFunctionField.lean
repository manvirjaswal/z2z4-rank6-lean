import Z2Z4Rank6.FunctionField
import Z2Z4Rank6.FamilyIdentities

/-!
# The quadratic function field of G

Proposition 7.2 of M. Jaswal, DOI 10.5281/zenodo.23437117.
G has equation η²=99m⁴−9998m²+970299. Its function field is a
quadratic root field over RatFuncℚ; the nonsquare and degree claims are proved.
-/

namespace Z2Z4Rank6.GFunctionField

open Polynomial

noncomputable section

def h {R : Type*} [CommRing R] (t : R) : R := 99*t^4-9998*t^2+970299
def hPolynomial : ℚ[X] := h Polynomial.X
abbrev Base := RatFunc ℚ
def d : Base := h RatFunc.X

theorem hPolynomial_image : algebraMap ℚ[X] Base hPolynomial=d := by
  simp [hPolynomial,h,d,RatFunc.algebraMap_X,map_ofNat]

theorem hPolynomial_leadingCoeff : hPolynomial.leadingCoeff=99 := by
  have hd : hPolynomial.natDegree=4 := by
    unfold hPolynomial h
    compute_degree!
  rw [Polynomial.leadingCoeff,hd]
  norm_num [hPolynomial,h,Polynomial.coeff_X]

theorem d_not_isSquare : ¬IsSquare d := by
  rw [← hPolynomial_image]
  apply FunctionField.not_isSquare_fraction_of_leadingCoeff
  rw [hPolynomial_leadingCoeff]
  norm_num [Rat.isSquare_natCast_iff]

instance d_nonsquare_fact : Fact (¬IsSquare d) := ⟨d_not_isSquare⟩
abbrev K := QuadraticAlgebra Base d 0
local instance fieldDecidableEq : DecidableEq K := Classical.decEq K

def m : K := algebraMap Base K RatFunc.X
def eta : K := QuadraticAlgebra.omega

theorem eta_sq : eta^2=h m := by
  have he : eta^2=algebraMap Base K d := by
    rw [eta,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [he]
  simp only [d,h,m,map_add,map_sub,map_mul,map_pow,map_ofNat]

theorem finrank_eq_two : Module.finrank Base K=2 := QuadraticAlgebra.finrank_eq_two _ _

theorem m_transcendental : Transcendental ℚ m := by
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem m_ne_zero : m ≠ 0 := by
  intro hm
  apply RatFunc.X_ne_zero (K:=ℚ)
  apply (algebraMap Base K).injective
  simpa only [map_zero,m] using hm

theorem chart_denominator_ne_zero : 99-m^2 ≠ 0 := by
  intro hz
  apply m_transcendental
  refine ⟨99-Polynomial.X^2,?_,?_⟩
  · intro hp
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) hp
    norm_num at he
  · simpa only [map_sub,map_pow,map_ofNat,aeval_X] using hz

theorem chart_numerator_ne_zero : eta-98*m ≠ 0 := by
  intro hz
  have him := congrArg QuadraticAlgebra.im hz
  have h98 : QuadraticAlgebra.im (98:K)=0 := rfl
  simp [eta,m,QuadraticAlgebra.im_mul,h98] at him

theorem field_adjoin_coordinates_eq_top :
    IntermediateField.adjoin ℚ ({m,eta} : Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({m,eta} : Set K)
  have hm : m ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have he : eta ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hC (r : ℚ) : algebraMap Base K (RatFunc.C r) ∈ S := by
    have hc : (algebraMap Base K).comp (RatFunc.C : ℚ →+* Base)=algebraMap ℚ K :=
      Subsingleton.elim _ _
    rw [← RingHom.comp_apply, hc]
    exact S.algebraMap_mem r
  have hpoly (p : ℚ[X]) : algebraMap Base K (algebraMap ℚ[X] Base p) ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add,map_add]; exact add_mem hp hq
    | monomial n r =>
      rw [RatFunc.algebraMap_monomial,map_mul,map_pow]
      exact mul_mem (hC r) (pow_mem hm n)
  have hbase (r : Base) : algebraMap Base K r ∈ S := by
    induction r using RatFunc.induction_on with
    | _ p q hq => rw [map_div₀]; exact div_mem (hpoly p) (hpoly q)
  apply top_unique
  intro z _
  change z ∈ S
  have hz : z=algebraMap Base K z.re+algebraMap Base K z.im*eta := by
    simpa only [Algebra.smul_def,mul_one,eta] using
      (QuadraticAlgebra.re_smul_add_im_smul z).symm
  rw [hz]
  exact add_mem (hbase _) (mul_mem (hbase _) he)

private def fiberPolynomial : ℚ[X] :=
  a Polynomial.X*b Polynomial.X*((a Polynomial.X)^2-(b Polynomial.X)^2)

private theorem fiberPolynomial_ne_zero : fiberPolynomial ≠ 0 := by
  intro hp
  have he := congrArg (Polynomial.eval (2:ℚ)) hp
  norm_num [fiberPolynomial,a,b] at he

theorem fiber_product_ne_zero : a m*b m*((a m)^2-(b m)^2) ≠ 0 := by
  have hinj := transcendental_iff_injective.mp m_transcendental
  have he : aeval m fiberPolynomial=a m*b m*((a m)^2-(b m)^2) := by
    simp [fiberPolynomial,a,b,map_ofNat]
  intro hz
  apply fiberPolynomial_ne_zero
  apply hinj
  simpa only [map_zero,he] using hz

instance genericFiberElliptic : (X m).IsElliptic := by
  have ha := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).1
  have hb := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp fiber_product_ne_zero).1).2
  have hab := (mul_ne_zero_iff.mp fiber_product_ne_zero).2
  have hd : (X m).Δ=16*(a m)^4*(b m)^4*((a m)^2-(b m)^2)^2 := by
    simp only [X,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
      WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  constructor
  rw [isUnit_iff_ne_zero,hd]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 4 ha))
    (pow_ne_zero 4 hb)) (pow_ne_zero 2 hab)

end
end Z2Z4Rank6.GFunctionField
