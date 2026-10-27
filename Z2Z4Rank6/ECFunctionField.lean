import Z2Z4Rank6.QuarticFunctionFieldHelpers
import Z2Z4Rank6.BaseCurveArithmetic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# The function field of the printed E_C cubic

The field is ℚ(x)[y]/(y²−x³−x²+137620x+10504000). Odd degree proves that
its defining rational function is nonsquare. Source: Jaswal Lemma 4.1, DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.ECFunctionField
open Polynomial
noncomputable section

abbrev Base := RatFunc ℚ
def cubicPolynomial : ℚ[X] := Polynomial.X^3+Polynomial.X^2-137620*Polynomial.X-10504000
def d : Base := RatFunc.X^3+RatFunc.X^2-137620*RatFunc.X-10504000

theorem cubicPolynomial_natDegree : cubicPolynomial.natDegree=3 := by
  unfold cubicPolynomial
  compute_degree!

theorem cubicPolynomial_image : algebraMap ℚ[X] Base cubicPolynomial=d := by
  simp [cubicPolynomial,d,RatFunc.algebraMap_X,map_ofNat]

theorem d_not_isSquare : ¬IsSquare d := by
  rw [←cubicPolynomial_image]
  apply not_isSquare_fraction_of_odd_degree
  rw [cubicPolynomial_natDegree]
  decide

instance ecFunctionFieldNonsquare : Fact (¬IsSquare d) := ⟨d_not_isSquare⟩
abbrev K := QuadraticAlgebra Base d 0
local instance ecFunctionFieldDecidableEq : DecidableEq K := Classical.decEq K

def x : K := algebraMap Base K RatFunc.X
def y : K := QuadraticAlgebra.omega

theorem y_sq : y^2=x^3+x^2-137620*x-10504000 := by
  have h : y^2=algebraMap Base K d := by
    rw [y,sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp only [map_zero,zero_mul,add_zero]
  rw [h]
  simp [d,x,map_ofNat]

theorem x_transcendental : Transcendental ℚ x := by
  apply (transcendental_algebraMap_iff (R:=ℚ) (algebraMap Base K).injective).mpr
  convert RatFunc.transcendental_X (K:=ℚ) using 1
  exact Subsingleton.elim _ _

theorem finrank_eq_two : Module.finrank Base K=2 := QuadraticAlgebra.finrank_eq_two _ _

theorem coordinate_expansion (z : K) :
    z=algebraMap Base K z.re+algebraMap Base K z.im*y := by
  simpa only [Algebra.smul_def,mul_one,y] using (QuadraticAlgebra.re_smul_add_im_smul z).symm

theorem field_adjoin_coordinates_eq_top : IntermediateField.adjoin ℚ ({x,y} : Set K)=⊤ := by
  let S := IntermediateField.adjoin ℚ ({x,y} : Set K)
  have hx : x∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hy : y∈S := IntermediateField.subset_adjoin _ _ (by simp)
  have hC (r : ℚ) : algebraMap Base K (RatFunc.C r)∈S := by
    have he : (algebraMap Base K).comp (RatFunc.C : ℚ→+*Base)=algebraMap ℚ K := Subsingleton.elim _ _
    rw [←RingHom.comp_apply,he]
    exact S.algebraMap_mem r
  have hpoly (p : ℚ[X]) : algebraMap Base K (algebraMap ℚ[X] Base p)∈S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | monomial n r =>
      simpa only [RatFunc.algebraMap_monomial,map_mul,map_pow,x] using
        S.mul_mem (hC r) (pow_mem hx n)
  have hbase (r : Base) : algebraMap Base K r∈S := by
    induction r using RatFunc.induction_on with
    | _ p q hq => simpa only [map_div₀] using S.div_mem (hpoly p) (hpoly q)
  apply top_unique
  intro z _
  change z∈S
  rw [coordinate_expansion z]
  exact S.add_mem (hbase _) (S.mul_mem (hbase _) hy)

end
end Z2Z4Rank6.ECFunctionField
