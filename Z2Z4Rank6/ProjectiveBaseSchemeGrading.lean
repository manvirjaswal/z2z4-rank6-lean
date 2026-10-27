import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Grading the quotient by a homogeneous ideal

The homogeneous-coordinate ring for Jaswal's projective base curve
(DOI 10.5281/zenodo.23437117, Section 3) is a quotient ring.
This file supplies its grading from the homogeneous components of the
polynomial ring.
-/
namespace Z2Z4Rank6.ProjectiveBaseSchemeGrading
noncomputable section
open scoped Classical DirectSum

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (I : Ideal A)

/-- Images of the homogeneous pieces in the quotient ring. -/
def component (n : ℕ) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

def componentMap (n : ℕ) : 𝒜 n →ₗ[R] component 𝒜 I n :=
  ((Ideal.Quotient.mkₐ R I).toLinearMap.comp (𝒜 n).subtype).codRestrict _
    (fun x => ⟨x,x.property,rfl⟩)

omit [GradedAlgebra 𝒜] in
@[simp] theorem componentMap_coe (n : ℕ) (x : 𝒜 n) :
    (componentMap 𝒜 I n x : A ⧸ I)=Ideal.Quotient.mk I x := rfl

instance componentGradedMonoid : SetLike.GradedMonoid (component 𝒜 I) where
  one_mem := ⟨1,SetLike.one_mem_graded 𝒜,rfl⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a,ha,rfl⟩ := hx
    obtain ⟨b,hb,rfl⟩ := hy
    exact ⟨a*b,SetLike.mul_mem_graded ha hb,(Ideal.Quotient.mkₐ R I).map_mul a b⟩

/-- Decompose first and then take the quotient of each homogeneous piece. -/
def decomposeBeforeQuotient : A →ₗ[R] ⨁ n,component 𝒜 I n :=
  (DirectSum.lmap (componentMap 𝒜 I)).comp
    (DirectSum.decomposeAlgEquiv 𝒜).toLinearMap

theorem decomposeBeforeQuotient_of_mem {n : ℕ} (x : A) (hx : x∈𝒜 n) :
    decomposeBeforeQuotient 𝒜 I x=
      DirectSum.of (fun n => component 𝒜 I n) n (componentMap 𝒜 I n ⟨x,hx⟩) := by
  simp only [decomposeBeforeQuotient,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
    DirectSum.decomposeAlgEquiv_apply,DirectSum.decompose_of_mem 𝒜 hx,DirectSum.lmap_of]

theorem decomposeBeforeQuotient_vanishes (hI : I.IsHomogeneous 𝒜) :
    Submodule.restrictScalars R (I : Submodule A A) ≤
      LinearMap.ker (decomposeBeforeQuotient 𝒜 I) := by
  intro x hx
  change decomposeBeforeQuotient 𝒜 I x=0
  apply DirectSum.ext
  intro n
  apply Subtype.ext
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 x n)=0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hI.mem_iff.mp hx) n)

def decomposeQuotient (hI : I.IsHomogeneous 𝒜) :
    (A ⧸ I) →ₗ[R] ⨁ n,component 𝒜 I n where
  __ := QuotientAddGroup.lift I.toAddSubgroup
    (decomposeBeforeQuotient 𝒜 I).toAddMonoidHom
    (decomposeBeforeQuotient_vanishes 𝒜 I hI)
  map_smul' := by
    intro r x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (decomposeBeforeQuotient 𝒜 I).map_smul r x

@[simp] theorem decomposeQuotient_mk (hI : I.IsHomogeneous 𝒜) (x : A) :
    decomposeQuotient 𝒜 I hI (Ideal.Quotient.mk I x)=decomposeBeforeQuotient 𝒜 I x := rfl

/-- The quotient images form a direct-sum decomposition. -/
@[instance_reducible]
def quotientDecomposition (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (component 𝒜 I) :=
  DirectSum.Decomposition.ofLinearMap (component 𝒜 I) (decomposeQuotient 𝒜 I hI) (by
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [LinearMap.comp_apply,LinearMap.id_apply,decomposeQuotient_mk]
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy => simp only [map_add,hx,hy]
    | homogeneous x =>
      rw [decomposeBeforeQuotient_of_mem 𝒜 I x x.property]
      simp)
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      intro x
      obtain ⟨a,ha,he⟩ := x.property
      have hx : x=componentMap 𝒜 I n ⟨a,ha⟩ := Subtype.ext he.symm
      subst x
      simp only [LinearMap.comp_apply,LinearMap.id_apply,DirectSum.lof_eq_of,
        DirectSum.coeLinearMap_of,componentMap_coe]
      change decomposeQuotient 𝒜 I hI (Ideal.Quotient.mk I a)=_
      rw [decomposeQuotient_mk,decomposeBeforeQuotient_of_mem 𝒜 I a ha])

/-- The homogeneous-ideal quotient is an internally graded algebra. -/
@[instance_reducible]
def quotientGradedAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (component 𝒜 I) :=
  { componentGradedMonoid 𝒜 I,quotientDecomposition 𝒜 I hI with }

end
end Z2Z4Rank6.ProjectiveBaseSchemeGrading
