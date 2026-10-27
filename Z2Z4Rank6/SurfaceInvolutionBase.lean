import Common.AlgebraicGeometry.ProjectiveLineSourceNaturality
import Common.AlgebraicGeometry.ProjGradedIsomorphism
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# The projective base involution of Lemma 3.1(c)

The homogeneous substitution is (U,V) ↦ (99V,U/99). Its square is the
identity on the graded polynomial ring, so it induces an
involution of Proj Q[U,V]. Its rational coordinate is 9801/n.
-/
namespace Z2Z4Rank6.SurfaceInvolution
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false

abbrev BaseRing := ProjectiveLine.Ring ℚ
abbrev Base := ProjectiveLine.scheme ℚ
abbrev F := RatFunc ℚ
local instance : Algebra ℚ F := RatFunc.instAlgebraOfPolynomial ℚ ℚ

def baseSubstitution : BaseRing →ₐ[ℚ] BaseRing :=
  MvPolynomial.aeval ![C (99 : ℚ)*X 1,C (1/99 : ℚ)*X 0]

def baseGraded : ProjectiveLine.grading ℚ →+*ᵍ ProjectiveLine.grading ℚ where
  toRingHom := baseSubstitution.toRingHom
  map_mem := by
    intro d p hp
    have h := MvPolynomial.IsHomogeneous.aeval hp
      (![C (99 : ℚ)*X 1,C (1/99 : ℚ)*X 0] : Fin 2 → BaseRing) (n:=1) (by
        intro i
        fin_cases i
        · simpa using (isHomogeneous_X ℚ 1).C_mul 99
        · simpa using (isHomogeneous_X ℚ 0).C_mul (1/99 : ℚ))
    change (baseSubstitution p).IsHomogeneous d
    simpa only [baseSubstitution,one_mul] using h

theorem baseGraded_square : baseGraded.comp baseGraded=
    GradedRingHom.id (ProjectiveLine.grading ℚ) := by
  have hh : baseSubstitution.toRingHom.comp baseSubstitution.toRingHom=RingHom.id BaseRing := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [baseSubstitution]
    · intro i
      change baseSubstitution (baseSubstitution (X i))=X i
      fin_cases i <;> simp [baseSubstitution,←mul_assoc,←MvPolynomial.C_mul]

  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun hh p

/-- Scheme automorphism induced by the involutive graded substitution. -/
def baseInvolution : Base ≅ Base :=
  Proj.isoOfInverse baseGraded baseGraded baseGraded_square baseGraded_square

theorem baseInvolution_square : baseInvolution.hom≫baseInvolution.hom=𝟙 Base :=
  baseInvolution.hom_inv_id

theorem baseInvolution_over : baseInvolution.hom≫ProjectiveLine.structureMap ℚ=
    ProjectiveLine.structureMap ℚ := by
  have hcoef : CommRingCat.ofHom (algebraMap ℚ (ProjectiveLine.grading ℚ 0)) ≫
      CommRingCat.ofHom baseGraded.gradedZeroRingHom=
      CommRingCat.ofHom (algebraMap ℚ (ProjectiveLine.grading ℚ 0)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Subtype.ext
    exact baseSubstitution.commutes a
  change Proj.map baseGraded _≫
      (Proj.toSpecZero _≫Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (ProjectiveLine.grading ℚ 0))))=_
  rw [←Category.assoc,Proj.map_toSpecZero,Category.assoc,←Spec.map_comp,hcoef]
  rfl

theorem reciprocal_transcendental : Transcendental ℚ (9801/(RatFunc.X : F)) := by
  intro h
  apply RatFunc.transcendental_X (K:=ℚ)
  have h' := (isAlgebraic_algebraMap (R:=ℚ) (A:=F) (9801 : ℚ)).mul h.inv
  have he : (algebraMap ℚ F (9801 : ℚ))/(9801/(RatFunc.X : F))=RatFunc.X := by
    norm_num
  rw [←div_eq_mul_inv] at h'
  rw [he] at h'
  exact h'

def reciprocalPolynomialMap : Polynomial ℚ →ₐ[ℚ] F := Polynomial.aeval (9801/(RatFunc.X : F))

def reciprocalFieldMap : F →ₐ[ℚ] F :=
  (RatFunc.liftRingHom reciprocalPolynomialMap.toRingHom
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp reciprocal_transcendental))).toRatAlgHom

@[simp] theorem reciprocalFieldMap_X : reciprocalFieldMap (RatFunc.X : F)=9801/RatFunc.X := by
  change RatFunc.liftRingHom _ _ (RatFunc.X : F)=_
  rw [RatFunc.liftRingHom_X]
  simp [reciprocalPolynomialMap]

theorem reciprocalFieldMap_square : reciprocalFieldMap.comp reciprocalFieldMap=AlgHom.id ℚ F := by
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A:=Polynomial ℚ)
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | monomial d a =>
    change reciprocalFieldMap (reciprocalFieldMap
      (algebraMap (Polynomial ℚ) F (Polynomial.monomial d a)))=_
    rw [RatFunc.algebraMap_monomial]
    have ha : RatFunc.C a=algebraMap ℚ F a := by exact (congrArg (fun f : ℚ →+* F => f a) RatFunc.algebraMap_eq_C).symm
    rw [ha]
    simp only [map_mul,map_pow,AlgHom.commutes,reciprocalFieldMap_X,map_div₀,map_ofNat]
    norm_num


def reciprocalFieldEquiv : F ≃ₐ[ℚ] F :=
  AlgEquiv.ofAlgHom reciprocalFieldMap reciprocalFieldMap
    reciprocalFieldMap_square reciprocalFieldMap_square

def genericBaseInvolution : Spec (CommRingCat.of F) ≅ Spec (CommRingCat.of F) :=
  Scheme.Spec.mapIso reciprocalFieldEquiv.toRingEquiv.toCommRingCatIso.op

end
end Z2Z4Rank6.SurfaceInvolution
