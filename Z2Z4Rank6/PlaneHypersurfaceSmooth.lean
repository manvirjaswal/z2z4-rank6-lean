import Z2Z4Rank6.AffineBaseSchemeSmooth

/-! A generic smoothness criterion for a plane hypersurface over Q.
The proof constructs finite submersive presentations on the two derivative
localizations and glues them using a proved unit-ideal premise.
-/
namespace Z2Z4Rank6.PlaneHypersurfaceSmooth
noncomputable section
open scoped Classical
open AlgebraicGeometry

abbrev P := MvPolynomial (Fin 2) ℚ
variable (p:P)
def relations (_:Fin 1) : P := p
def ideal : Ideal P := Ideal.span (Set.range (relations p))
abbrev Ring := P⧸ideal p
def derivative (i:Fin 2) : Ring p := Ideal.Quotient.mk (ideal p) (MvPolynomial.pderiv i p)
def columnMap (i:Fin 2) : Fin 1→Fin 2 := fun _=>i

def prePresentation (i:Fin 2) :
    Algebra.PreSubmersivePresentation ℚ (Ring p) (Fin 2) (Fin 1) :=
  Algebra.PreSubmersivePresentation.naive (v:=relations p) (columnMap i)
    (fun a b _=>Subsingleton.elim a b)

theorem prePresentation_jacobian (i:Fin 2) :
    (prePresentation p i).jacobian=derivative p i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_fin_one]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

abbrev Chart (i:Fin 2) := Localization.Away (derivative p i)
def chartPrePresentation (i:Fin 2) :
    Algebra.PreSubmersivePresentation ℚ (Chart p i) (Unit⊕Fin 2) (Unit⊕Fin 1) :=
  (Algebra.PreSubmersivePresentation.localizationAway (Chart p i) (derivative p i)).comp
    (prePresentation p i)

theorem chartPrePresentation_jacobian_isUnit (i:Fin 2) :
    IsUnit (chartPrePresentation p i).jacobian := by
  have hq : IsUnit (algebraMap (Ring p) (Chart p i) (derivative p i)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [chartPrePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,Algebra.smul_def,
    prePresentation_jacobian]
  exact hq.mul hq

def chartPresentation (i:Fin 2) :
    Algebra.SubmersivePresentation ℚ (Chart p i) (Unit⊕Fin 2) (Unit⊕Fin 1) where
  __:=chartPrePresentation p i
  jacobian_isUnit:=chartPrePresentation_jacobian_isUnit p i

instance chart_standard_smooth (i:Fin 2) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (Chart p i) :=
  (chartPresentation p i).isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])

theorem locally_standard_smooth (h:Ideal.span (Set.range (derivative p))=⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap ℚ (Ring p)) := by
  refine ⟨Set.range (derivative p),h,?_⟩
  rintro t ⟨i,rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 1
    ((algebraMap (Ring p) (Chart p i)).comp (algebraMap ℚ (Ring p)))
  rw [←IsScalarTower.algebraMap_eq ℚ (Ring p) (Chart p i),
    RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact chart_standard_smooth p i

/-- This conclusion is the scheme-morphism predicate. -/
theorem structureMap_smooth (h:Ideal.span (Set.range (derivative p))=⊤) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Ring p)))) := by
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 1)]
  exact locally_standard_smooth p h

end
end Z2Z4Rank6.PlaneHypersurfaceSmooth
