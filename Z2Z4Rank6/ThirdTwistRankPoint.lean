import Z2Z4Rank6.ThirdTwistSpecialization
import Z2Z4Rank6.GusicTadicCompatibility
import Z2Z4Rank6.MordellWeil

/-!
# The third-twist section and its infinite-order specialization

The x-coordinate is the one printed after Proposition 7.2 of Jaswal,
DOI 10.5281/zenodo.23437117. Its ordinate is verified directly. At m=42 the
doubled point on the normalized integral model has an odd denominator.
The torsion hypothesis is Silverman's VII.3.4.
-/
namespace Z2Z4Rank6.ThirdTwist
noncomputable section
open Polynomial GusicTadic Common.WeierstrassCoordinates

def sectionX {R : Type*} [CommRing R] (m : R) : R :=
  49*m^2*(m^2-121)*(m^2-1)*(11*m^2-1971)^2

def sectionY {R : Type*} [CommRing R] (m : R) : R :=
  1715*m*(m^2-121)*(m^2-99)*(m^2-1)*(11*m^2-1971)*(25*m^2-81)*
    (m^4-2*m^2+9801)

def surfaceSectionX {R : Type*} [CommRing R] (n : R) : R :=
  49*(n-121)*(n-1)*n^2*(11*n-1971)^2

def surfaceSectionY {R : Type*} [CommRing R] (n : R) : R :=
  1715*n^2*(n-121)*(n-99)*(n-1)*(11*n-1971)*(25*n-81)*(n^2-2*n+9801)

theorem surface_section_equation {R : Type*} [CommRing R] (n : R) :
    (surfaceSectionY n)^2=surfaceSectionX n*((surfaceSectionX n)^2+
      n*(4*n+45)*surfaceS n*surfaceSectionX n+(n*(4*n+45))^2*(surfaceW n)^2) := by
  unfold surfaceSectionX surfaceSectionY surfaceS surfaceW
  ring

theorem section_base_change {R : Type*} [CommRing R] (m : R) :
    surfaceSectionX (m^2)=m^2*sectionX m ∧
      surfaceSectionY (m^2)=m^3*sectionY m := by
  unfold surfaceSectionX surfaceSectionY sectionX sectionY
  constructor <;> ring

theorem section_equation {R : Type*} [CommRing R] (m : R) :
    (sectionY m)^2=sectionX m*(sectionX m+q3 m*(a m)^2)*(sectionX m+q3 m*(b m)^2) := by
  unfold sectionX sectionY q3 a b
  ring

theorem section_affine_equation {R : Type*} [CommRing R] (m : R) :
    (twistModel (q3 m) (a m) (b m)).toAffine.Equation (sectionX m) (sectionY m) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [twistModel,zero_mul,add_zero]
  linear_combination section_equation m

theorem q3_image : polyToRF q3Poly=q3 (RatFunc.X : RF) := by
  simp [polyToRF,q3Poly,q3,map_ofNat]

def genericPoint : (genericModel (twistPolynomial 0)).toAffine.Point :=
  .mk (x:=sectionX (RatFunc.X : RF)) (y:=sectionY RatFunc.X) (by
    change (twistModel (polyToRF q3Poly) (a RatFunc.X) (b RatFunc.X)).toAffine.Equation _ _
    rw [q3_image]
    exact section_affine_equation _)

def fiberPoint : RationalPoints (fiber 0) :=
  .mk (x:=sectionX (42:ℚ)) (y:=sectionY (42:ℚ)) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [fiber,fiberModel,twistModel,twistPolynomial,parameter,evalAt,q3Poly,q3,
      sectionX,sectionY,a,b])

def normalizedPoint : RationalPoints (curve 0) :=
  .mk (x:=2130125485931716) (y:=123116485964910425382850) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve,splitWeierstrass,r2,r3,D,A,B])

def normalizedDouble : RationalPoints (curve 0) :=
  .mk (x:=22385131643240097213087868451641/70367258252012176)
    (y:=260061140688234289684149358105007182494514598275/18666201283358043458528576) (by
      rw [WeierstrassCurve.Affine.equation_iff]
      norm_num [curve,splitWeierstrass,r2,r3,D,A,B])

theorem normalizedPoint_double : (2:ℕ) • normalizedPoint=normalizedDouble := by
  norm_num [normalizedPoint,normalizedDouble,WeierstrassCurve.Affine.Point.mk,
    two_nsmul,WeierstrassCurve.Affine.Point.add_def,WeierstrassCurve.Affine.Point.add,
    WeierstrassCurve.Affine.negY,WeierstrassCurve.Affine.slope,WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,
    curve,splitWeierstrass,r2,r3,D,A,B]

theorem curve_integral (k : Fin 4) : IntegralWeierstrass (curve k) := by
  refine ⟨⟨0,r2 k+r3 k,0,r2 k*r3 k,0⟩,?_⟩
  ext <;> simp [WeierstrassCurve.map,curve,splitWeierstrass,add_comm]

theorem normalizedPoint_infinite_order (hOdd : OddPrimeTorsionIntegrality) :
    ¬IsOfFinAddOrder normalizedPoint := by
  intro h
  have h2 : IsOfFinAddOrder normalizedDouble := normalizedPoint_double ▸ h.nsmul
  exact (hOdd (curve 0) inferInstance (curve_integral 0) 7 (by decide) (by decide)
    _ _ _ h2) (by norm_num)

private theorem encode_variableChange {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (C : WeierstrassCurve.VariableChange F)
    (P : (C • W).toAffine.Point) :
    encode (VariableChangePoints.pointEquiv W C P)=
      (encode P).map (fun q => (VariableChangePoints.coordX C q.1,
        VariableChangePoints.coordY C q.1 q.2)) := by
  cases P <;> rfl

theorem fiberEquiv_point : fiberEquiv 0 fiberPoint=normalizedPoint := by
  apply encode_injective
  simp only [fiberEquiv,AddEquiv.trans_apply,encode_variableChange,
    PointScaling.encode_pointCongr]
  norm_num [fiberPoint,normalizedPoint,WeierstrassCurve.Affine.Point.mk,
    encode,sectionX,sectionY,VariableChangePoints.coordX,VariableChangePoints.coordY,
    scalingChange,scale]

private theorem sectionX_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (m : R) : f (sectionX m)=sectionX (f m) := by
  simp [sectionX,map_ofNat]

private theorem sectionY_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (m : R) : f (sectionY m)=sectionY (f m) := by
  simp [sectionY,map_ofNat]

theorem specialization_point
    (σ : (genericModel (twistPolynomial 0)).toAffine.Point→+RationalPoints (fiber 0))
    (hσ : CanonicalSpecializationAt _ _ (parameter 0) σ) : σ genericPoint=fiberPoint := by
  apply encode_injective
  have hx : algebraMap ℚ[X] RF (sectionX (Polynomial.X:ℚ[X]))=sectionX (RatFunc.X:RF) := by
    rw [sectionX_map,RatFunc.algebraMap_X]
  have hy : algebraMap ℚ[X] RF (sectionY (Polynomial.X:ℚ[X]))=sectionY (RatFunc.X:RF) := by
    rw [sectionY_map,RatFunc.algebraMap_X]
  have hn : (genericModel (twistPolynomial 0)).toAffine.Nonsingular
      (algebraMap ℚ[X] RF (sectionX (Polynomial.X:ℚ[X])))
      (algebraMap ℚ[X] RF (sectionY (Polynomial.X:ℚ[X]))) := by
    rw [hx,hy]
    exact (genericModel (twistPolynomial 0)).toAffine.equation_iff_nonsingular.mp
      (by change (twistModel (polyToRF q3Poly) (a RatFunc.X) (b RatFunc.X)).toAffine.Equation _ _
          rw [q3_image];exact section_affine_equation _)
  have he := hσ.polynomial_coordinates (sectionX (Polynomial.X:ℚ[X]))
    (sectionY (Polynomial.X:ℚ[X])) hn
  have hp : WeierstrassCurve.Affine.Point.some _ _ hn=genericPoint := by
    apply encode_injective
    simp only [genericPoint,WeierstrassCurve.Affine.Point.mk,encode,hx,hy]
  rw [hp] at he
  simpa [fiberPoint,WeierstrassCurve.Affine.Point.mk,encode,sectionX,sectionY,parameter] using he

theorem genericPoint_infinite_order (hGT : GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) : ¬IsOfFinAddOrder genericPoint := by
  intro h
  obtain ⟨σ,hσ,_⟩ := injective_specialization hGT 0
  have hf : IsOfFinAddOrder fiberPoint := by
    rw [←specialization_point σ hσ]
    exact σ.isOfFinAddOrder h
  have hn : IsOfFinAddOrder normalizedPoint := by
    rw [←fiberEquiv_point]
    exact (fiberEquiv 0).toAddMonoidHom.isOfFinAddOrder hf
  exact normalizedPoint_infinite_order hOdd hn

theorem generic_rank_at_least_one (hGT : GusicTadicTheorem11)
    (hOdd : OddPrimeTorsionIntegrality) :
    1≤Module.rank ℤ (genericModel (twistPolynomial 0)).toAffine.Point := by
  rw [Cardinal.one_le_iff_ne_zero]
  intro hz
  have ht := (Module.rank_eq_zero_iff_isTorsion (R:=ℤ)
    (M:=(genericModel (twistPolynomial 0)).toAffine.Point)).mp hz
  exact genericPoint_infinite_order hGT hOdd
    ((isAddTorsion_iff_isTorsion_int.mpr ht) genericPoint)

end
end Z2Z4Rank6.ThirdTwist
