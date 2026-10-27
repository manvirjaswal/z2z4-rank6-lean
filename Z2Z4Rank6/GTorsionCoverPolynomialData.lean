import Z2Z4Rank6.GQuarticGeometry
import Z2Z4Rank6.TorsionCoverPolynomialData

/-! Polynomial data for the two signed double covers of G.
The radicands have degrees 4 and 8. Exact rational Euclidean certificates
prove separability in both the affine and infinity charts. -/
namespace Z2Z4Rank6.GTorsionCoverPolynomialData
noncomputable section
open Polynomial
abbrev sign := TorsionHyperelliptic.sign

def affineRadicand (ε : Bool) : Fin 2→ℚ[X] :=
  ![gQuarticPolynomial,C (sign ε)*a Polynomial.X*b Polynomial.X]
def infinityRadicand (ε : Bool) : Fin 2→ℚ[X] :=
  ![99-9998*Polynomial.X^2+970299*Polynomial.X^4,
    C (sign ε)*HeightInvariantForms.binaryA Polynomial.X 1*
      HeightInvariantForms.binaryB Polynomial.X 1]
def affineCore : ℚ[X] :=
  gQuarticPolynomial*a Polynomial.X*b Polynomial.X
def infinityCore : ℚ[X] :=
  (99-9998*Polynomial.X^2+970299*Polynomial.X^4)*
    HeightInvariantForms.binaryA Polynomial.X 1*HeightInvariantForms.binaryB Polynomial.X 1
abbrev affineProduct (ε : Bool) : ℚ[X] := ∏i,affineRadicand ε i
abbrev infinityProduct (ε : Bool) : ℚ[X] := ∏i,infinityRadicand ε i

def affineBezoutA : ℚ[X] := Polynomial.C (1842465590939116544381/1053944139016938244200242240612966400000000000000 : ℚ)*Polynomial.X^10+Polynomial.C (-1150044799923283942447133107/78255352322007664631867986365512755200000000000000 : ℚ)*Polynomial.X^8+Polynomial.C (518297189438730893687895351371/156510704644015329263735972731025510400000000000000 : ℚ)*Polynomial.X^6+Polynomial.C (-8224310852869550631942065111069/26085117440669221543955995455170918400000000000000 : ℚ)*Polynomial.X^4+Polynomial.C (478259753152572571985214462757/31937701182331461945461886079180800000000000000 : ℚ)*Polynomial.X^2+Polynomial.C (-1/4567120204744251 : ℚ)
def affineBezoutB : ℚ[X] := Polynomial.C (-1842465590939116544381/12647329668203258930402906887355596800000000000000 : ℚ)*Polynomial.X^11+Polynomial.C (368118330725607269862551699/250417127430424526821977556369640816640000000000000 : ℚ)*Polynomial.X^9+Polynomial.C (-52475533703617132885219384919/125208563715212263410988778184820408320000000000000 : ℚ)*Polynomial.X^7+Polynomial.C (6695193408763652589685955349379/125208563715212263410988778184820408320000000000000 : ℚ)*Polynomial.X^5+Polynomial.C (-295827810422449027009285960637/76650482837595508669108526590033920000000000000 : ℚ)*Polynomial.X^3+Polynomial.C (4564943301100890408138410857/39103399060093617319206472089600000000000000 : ℚ)*Polynomial.X^1
theorem affine_core_bezout :
    affineBezoutA*affineCore+affineBezoutB*derivative affineCore=1 := by
  apply Polynomial.funext
  intro x
  norm_num [affineBezoutA,affineBezoutB,affineCore,gQuarticPolynomial,a,b,
    HeightInvariantForms.binaryA,HeightInvariantForms.binaryB,
    derivative_add,derivative_sub,derivative_mul,derivative_pow]
  ring

theorem affine_core_separable : affineCore.Separable :=
  ⟨affineBezoutA,affineBezoutB,affine_core_bezout⟩

theorem affine_product_factor (ε : Bool) :
    affineProduct ε=C (sign ε)*affineCore := by
  rw [affineProduct,Fin.prod_univ_two]
  dsimp [affineRadicand,affineCore]
  ring

theorem affine_product_separable (ε : Bool) : (affineProduct ε).Separable := by
  rw [affine_product_factor]
  exact affine_core_separable.unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (TorsionHyperelliptic.sign_ne_zero ε)))

theorem affine_radicand_natDegree (ε : Bool) (i : Fin 2) :
    (affineRadicand ε i).natDegree=![4,8] i := by
  cases ε <;> fin_cases i <;>
    norm_num [affineRadicand,sign,TorsionHyperelliptic.sign,gQuarticPolynomial,a,b,
      HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] <;> compute_degree!

theorem affine_product_natDegree (ε : Bool) : (affineProduct ε).natDegree=12 := by
  cases ε <;> rw [affine_product_factor] <;>
    norm_num [sign,TorsionHyperelliptic.sign,affineCore,gQuarticPolynomial,a,b,
      HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] <;> compute_degree!

def infinityBezoutA : ℚ[X] := Polynomial.C (15611803018412050764888972543592029/104883737894297600000000000000 : ℚ)*Polynomial.X^10+Polynomial.C (-3347661957962287458217532419766979/26220934473574400000000000000 : ℚ)*Polynomial.X^8+Polynomial.C (153934265263303075425304919357187/52441868947148800000000000000 : ℚ)*Polynomial.X^6+Polynomial.C (-8224310852869550631942065111069/288430279209318400000000000000 : ℚ)*Polynomial.X^4+Polynomial.C (478259753152572571985214462757/3461163350511820800000000000000 : ℚ)*Polynomial.X^2+Polynomial.C (-1/4851 : ℚ)
def infinityBezoutB : ℚ[X] := Polynomial.C (-5203934339470683588296324181197343/419534951577190400000000000000 : ℚ)*Polynomial.X^11+Polynomial.C (1071554544554178025021092152964003/83906990315438080000000000000 : ℚ)*Polynomial.X^9+Polynomial.C (-15585233509974288466910157320943/41953495157719040000000000000 : ℚ)*Polynomial.X^7+Polynomial.C (6695193408763652589685955349379/1384465340204728320000000000000 : ℚ)*Polynomial.X^5+Polynomial.C (-295827810422449027009285960637/8306792041228369920000000000000 : ℚ)*Polynomial.X^3+Polynomial.C (4564943301100890408138410857/41533960206141849600000000000000 : ℚ)*Polynomial.X^1
theorem infinity_core_bezout :
    infinityBezoutA*infinityCore+infinityBezoutB*derivative infinityCore=1 := by
  apply Polynomial.funext
  intro x
  norm_num [infinityBezoutA,infinityBezoutB,infinityCore,gQuarticPolynomial,a,b,
    HeightInvariantForms.binaryA,HeightInvariantForms.binaryB,
    derivative_add,derivative_sub,derivative_mul,derivative_pow]
  ring

theorem infinity_core_separable : infinityCore.Separable :=
  ⟨infinityBezoutA,infinityBezoutB,infinity_core_bezout⟩

theorem infinity_product_factor (ε : Bool) :
    infinityProduct ε=C (sign ε)*infinityCore := by
  rw [infinityProduct,Fin.prod_univ_two]
  dsimp [infinityRadicand,infinityCore]
  ring

theorem infinity_product_separable (ε : Bool) : (infinityProduct ε).Separable := by
  rw [infinity_product_factor]
  exact infinity_core_separable.unit_mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (TorsionHyperelliptic.sign_ne_zero ε)))

theorem infinity_radicand_natDegree (ε : Bool) (i : Fin 2) :
    (infinityRadicand ε i).natDegree=![4,8] i := by
  cases ε <;> fin_cases i <;>
    norm_num [infinityRadicand,sign,TorsionHyperelliptic.sign,gQuarticPolynomial,a,b,
      HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] <;> compute_degree!

theorem infinity_product_natDegree (ε : Bool) : (infinityProduct ε).natDegree=12 := by
  cases ε <;> rw [infinity_product_factor] <;>
    norm_num [sign,TorsionHyperelliptic.sign,infinityCore,gQuarticPolynomial,a,b,
      HeightInvariantForms.binaryA,HeightInvariantForms.binaryB] <;> compute_degree!

end
end Z2Z4Rank6.GTorsionCoverPolynomialData
