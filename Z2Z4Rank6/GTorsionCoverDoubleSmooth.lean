module

public import Z2Z4Rank6.AffineBaseSchemeSmooth
public import Z2Z4Rank6.DoubleSquareCover
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# Smoothness of a double square-root cover

For y_i²=f_i(t), separability of the product f0*f1 proves that
three maximal Jacobian minors generate the unit ideal. The proof constructs
finite submersive presentations for the three localizations, then
proves the Mathlib scheme-morphism smoothness predicate.
This generic elementary calculation applies to the torsion covers in
Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(c).
-/
namespace Z2Z4Rank6.DoubleSquareCoverSmooth
noncomputable section
open scoped Classical BigOperators
open AlgebraicGeometry Polynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev P := DoubleSquareCover.PolynomialRing
variable (f:Fin 2→ℚ[X])
abbrev relation := DoubleSquareCover.relation
abbrev ideal := DoubleSquareCover.definingIdeal
abbrev Ring := DoubleSquareCover.CoordinateRing
abbrev parameter := DoubleSquareCover.parameter
abbrev root := DoubleSquareCover.root
def rootDerivative (i:Fin 2) : Ring f := (Polynomial.aeval (parameter f)) (f i).derivative

abbrev mk_aeval := DoubleSquareCover.quotient_aeval
abbrev root_sq := DoubleSquareCover.root_sq

def minorFactor (i:Fin 3) : Ring f :=
  ![root f 0*root f 1,rootDerivative f 0*root f 1,rootDerivative f 1*root f 0] i

theorem product_eval : (Polynomial.aeval (parameter f)) (∏i,f i)=
    (root f 0*root f 1)^2 := by
  simp only [Fin.prod_univ_two,map_mul,←root_sq]
  ring

theorem derivative_product_eval : (Polynomial.aeval (parameter f)) (∏i,f i).derivative=
    rootDerivative f 0*root f 1^2+rootDerivative f 1*root f 0^2 := by
  simp only [Fin.prod_univ_two,derivative_mul,map_add,map_mul,←root_sq,rootDerivative]
  ring

/-- The three minor factors generate the unit ideal. -/
theorem minorFactors_span_top (hs:(∏i,f i).Separable) :
    Ideal.span (Set.range (minorFactor f))=⊤ := by
  let J : Ideal (Ring f) := Ideal.span (Set.range (minorFactor f))
  have h0 : minorFactor f 0∈J := Ideal.subset_span ⟨0,rfl⟩
  have h1 : minorFactor f 1∈J := Ideal.subset_span ⟨1,rfl⟩
  have h2 : minorFactor f 2∈J := Ideal.subset_span ⟨2,rfl⟩
  have hF : (Polynomial.aeval (parameter f)) (∏i,f i)∈J := by
    rw [product_eval]
    simpa only [minorFactor,Matrix.cons_val_zero,sq] using J.mul_mem_left (minorFactor f 0) h0
  have hF' : (Polynomial.aeval (parameter f)) (∏i,f i).derivative∈J := by
    rw [derivative_product_eval]
    have hsum := J.add_mem
      (J.mul_mem_left (root f 1) h1) (J.mul_mem_left (root f 0) h2)
    change (root f 1)*(rootDerivative f 0*root f 1)+
      (root f 0)*(rootDerivative f 1*root f 0)∈J at hsum
    convert hsum using 1; ring
  obtain ⟨A,B,hAB⟩ := hs
  have he := congrArg (Polynomial.aeval (parameter f)) hAB
  simp only [map_add,map_mul,map_one] at he
  apply (Ideal.eq_top_iff_one _).mpr
  rw [←he]
  exact J.add_mem (J.mul_mem_left _ hF) (J.mul_mem_left _ hF')

/-- The three choices of two Jacobian columns. -/
def columnMap (i:Fin 3) : Fin 2→Fin 3 :=
  ![![1,2],![0,2],![0,1]] i

theorem columnMap_injective (i:Fin 3) : Function.Injective (columnMap i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [columnMap] at h ⊢

def prePresentation (i:Fin 3) :
    Algebra.PreSubmersivePresentation ℚ (Ring f) (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v:=relation f) (columnMap i) (columnMap_injective i)

def minorCoefficient (i:Fin 3) : ℚ := ![4,-2,2] i

theorem minorCoefficient_ne_zero (i:Fin 3) : minorCoefficient i≠0 := by
  fin_cases i <;> norm_num [minorCoefficient]

theorem pderiv_relation (i:Fin 2) (j:Fin 3) :
    MvPolynomial.pderiv j (relation f i)=
      2*MvPolynomial.X i.succ*Pi.single (M:=fun _ :Fin 3=>P) j (1:P) i.succ-
      (Polynomial.aeval (MvPolynomial.X (0:Fin 3))) (f i).derivative*
        Pi.single (M:=fun _ :Fin 3=>P) j (1:P) 0 := by
  change MvPolynomial.pderiv j ((MvPolynomial.X i.succ)^2-
    Polynomial.aeval (MvPolynomial.X (0:Fin 3)) (f i))=_
  rw [map_sub,MvPolynomial.pderiv_pow,Derivation.map_aeval]
  simp only [MvPolynomial.pderiv_X,Nat.reduceSub,pow_one,Algebra.smul_def,Nat.cast_ofNat,Algebra.algebraMap_self_apply]

/-- Exact maximal-minor determinants in the quotient. -/
theorem prePresentation_jacobian (i:Fin 3) :
    (prePresentation f i).jacobian=
      algebraMap ℚ (Ring f) (minorCoefficient i)*minorFactor f i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have hm : (prePresentation f i).jacobiMatrix=
      fun j k :Fin 2=>MvPolynomial.pderiv (columnMap i j) (relation f k) := by
    ext j k
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    rfl
  rw [hm]
  change Ideal.Quotient.mk (ideal f)
    (Matrix.det (fun j k :Fin 2=>MvPolynomial.pderiv (columnMap i j) (relation f k)))=_
  rw [Matrix.det_fin_two]
  simp only [-Matrix.cons_val,pderiv_relation]
  fin_cases i <;>
    simp [-Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
      columnMap,minorCoefficient,minorFactor,map_ofNat,mk_aeval,rootDerivative,DoubleSquareCover.root,DoubleSquareCover.coordinate] <;> ring

abbrev Chart (i:Fin 3) := Localization.Away (minorFactor f i)
def chartPrePresentation (i:Fin 3) :
    Algebra.PreSubmersivePresentation ℚ (Chart f i) (Unit⊕Fin 3) (Unit⊕Fin 2) :=
  (Algebra.PreSubmersivePresentation.localizationAway (Chart f i) (minorFactor f i)).comp
    (prePresentation f i)

theorem chartPrePresentation_jacobian_isUnit (i:Fin 3) :
    IsUnit (chartPrePresentation f i).jacobian := by
  have hq : IsUnit (algebraMap (Ring f) (Chart f i) (minorFactor f i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hc : IsUnit (algebraMap ℚ (Ring f) (minorCoefficient i)) :=
    (isUnit_iff_ne_zero.mpr (minorCoefficient_ne_zero i)).map (algebraMap ℚ (Ring f))
  have hP : IsUnit (algebraMap (Ring f) (Chart f i) (prePresentation f i).jacobian) := by
    rw [prePresentation_jacobian,map_mul]
    exact (hc.map (algebraMap (Ring f) (Chart f i))).mul hq
  rw [chartPrePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,Algebra.smul_def]
  exact hP.mul hq

def chartPresentation (i:Fin 3) :
    Algebra.SubmersivePresentation ℚ (Chart f i) (Unit⊕Fin 3) (Unit⊕Fin 2) where
  __:=chartPrePresentation f i
  jacobian_isUnit:=chartPrePresentation_jacobian_isUnit f i
instance chart_standard_smooth (i:Fin 3) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Chart f i) :=
  (chartPresentation f i).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem locally_standard_smooth (hs:(∏i,f i).Separable) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (Ring f)) := by
  refine ⟨Set.range (minorFactor f),minorFactors_span_top f hs,?_⟩
  rintro t ⟨i,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap (Ring f) (Chart f i)).comp (algebraMap ℚ (Ring f)))
  rw [←IsScalarTower.algebraMap_eq ℚ (Ring f) (Chart f i),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact chart_standard_smooth f i

/-- Smoothness is proved for the Spec of the quotient. -/
theorem structureMap_smooth (hs:(∏i,f i).Separable) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Ring f)))) := by
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 1)]
  exact locally_standard_smooth f hs

end
end Z2Z4Rank6.DoubleSquareCoverSmooth
