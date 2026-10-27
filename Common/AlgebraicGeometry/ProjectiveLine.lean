module

public import Common.AlgebraicGeometry.ProjValuedPoint
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The projective line over a field

The scheme is Proj k[U,V] with its standard grading. Structural map,
properness and the canonical finite/infinity coordinate points are
constructed directly. The generic point uses (T:1) over k(T).
-/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open scoped Classical
open CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

abbrev Ring := MvPolynomial (Fin 2) k
def grading : ℕ → Submodule k (Ring k) := MvPolynomial.homogeneousSubmodule (Fin 2) k
instance gradedAlgebra : GradedAlgebra (grading k) := MvPolynomial.gradedAlgebra

def coordinate (i : Fin 2) : Ring k := X i
theorem coordinate_degree (i : Fin 2) : coordinate k i∈grading k 1 := isHomogeneous_X k i

def scheme : Scheme := Proj (grading k)
def structureMap : scheme k ⟶ Spec (CommRingCat.of k) := ProjFieldPoint.structureMap (grading k)

instance gradeZero_nontrivial : Nontrivial (grading k 0) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h : (0 : Ring k)=1)

instance gradeZero_scalarTower : IsScalarTower k (grading k 0) (Ring k) :=
  IsScalarTower.of_algebraMap_eq' (R:=k) (S:=grading k 0) (A:=Ring k) rfl

theorem degreeZero_eq_coefficient (r : grading k 0) :
    ∃ a : k,r=algebraMap k (grading k 0) a := by
  have hp : (r : Ring k).IsHomogeneous 0 := r.property
  have he : (r : Ring k)=C ((r : Ring k).coeff 0) :=
    hp.weightedHomogeneousComponent_same.symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero (r : Ring k) (by simp))
  exact ⟨(r : Ring k).coeff 0,Subtype.ext he⟩

def degreeZeroEquiv : k ≃+* grading k 0 :=
  RingEquiv.ofBijective (algebraMap k (grading k 0))
    ⟨(algebraMap k (grading k 0)).injective,fun r=>by
      obtain ⟨a,ha⟩ := degreeZero_eq_coefficient k r
      exact ⟨a,ha.symm⟩⟩

instance coordinateRing_finiteType : Algebra.FiniteType (grading k 0) (Ring k) :=
  Algebra.FiniteType.of_restrictScalars_finiteType k (grading k 0) (Ring k)

instance proper : IsProper (structureMap k) := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))) := by
    change IsIso (Scheme.Spec.mapIso (degreeZeroEquiv k).toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap,ProjFieldPoint.structureMap]
  infer_instance

variable (K : Type) [Field K] [Algebra k K]

def affinePoint (t : K) : Spec (CommRingCat.of K) ⟶ scheme k :=
  ProjValuedPoint.point (grading k) (MvPolynomial.aeval ![t,1])
    (by decide : 0<1) (coordinate k 1) (coordinate_degree k 1) (by simp [coordinate])

theorem affinePoint_over (t : K) : affinePoint k K t≫structureMap k=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  ProjValuedPoint.point_over (grading k) (MvPolynomial.aeval ![t,1])
    (by decide : 0<1) (coordinate k 1) (coordinate_degree k 1) (by simp [coordinate])

def infinityPoint : Spec (CommRingCat.of K) ⟶ scheme k :=
  ProjValuedPoint.point (grading k) (MvPolynomial.aeval ![(1:K),0])
    (by decide : 0<1) (coordinate k 0) (coordinate_degree k 0) (by simp [coordinate])

theorem infinityPoint_over : infinityPoint k K≫structureMap k=
    Spec.map (CommRingCat.ofHom (algebraMap k K)) :=
  ProjValuedPoint.point_over (grading k) (MvPolynomial.aeval ![(1:K),0])
    (by decide : 0<1) (coordinate k 0) (coordinate_degree k 0) (by simp [coordinate])

def genericPoint : Spec (CommRingCat.of (RatFunc k)) ⟶ scheme k :=
  affinePoint k (RatFunc k) RatFunc.X

theorem genericPoint_over : genericPoint k≫structureMap k=
    Spec.map (CommRingCat.ofHom (algebraMap k (RatFunc k))) :=
  affinePoint_over k (RatFunc k) RatFunc.X

end
end AlgebraicGeometry.ProjectiveLine
