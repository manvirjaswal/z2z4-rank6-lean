module

public import Common.AlgebraicGeometry.ProjectiveLine
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

/-!
# Affine coordinate charts of the projective line

The chart rings are homogeneous localizations. Their coordinate ratios
generate the rings over the coefficient field. All maps below are the
Proj open immersions and localization maps.
-/
namespace AlgebraicGeometry.ProjectiveLine.Charts
noncomputable section
open scoped Classical BigOperators
open MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

abbrev ChartRing (i : Fin 2) := HomogeneousLocalization.Away (grading k) (coordinate k i)
abbrev LocalizedRing (i : Fin 2) := Localization.Away (coordinate k i)

instance chartAlgebra (i : Fin 2) : Algebra k (ChartRing k i) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading k) (Submonoid.powers (coordinate k i))).comp
    (algebraMap k (grading k 0))).toAlgebra

def ratio (i j : Fin 2) : ChartRing k i :=
  HomogeneousLocalization.Away.mk (grading k) (coordinate_degree k i) 1 (coordinate k j)
    (by simpa using coordinate_degree k j)

def inverseCoordinate (i : Fin 2) : LocalizedRing k i :=
  IsLocalization.Away.invSelf (coordinate k i)

theorem coordinate_mul_inverse (i : Fin 2) :
    algebraMap (Ring k) (LocalizedRing k i) (coordinate k i)*inverseCoordinate k i=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (i j : Fin 2) :
    (ratio k i j).val=algebraMap (Ring k) (LocalizedRing k i) (coordinate k j)*
      inverseCoordinate k i := by
  simp only [ratio,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one,inverseCoordinate,IsLocalization.Away.invSelf]

@[simp] theorem ratio_self (i : Fin 2) : ratio k i i=1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio_val,HomogeneousLocalization.val_one,coordinate_mul_inverse]

theorem coordinate_adjoin : Algebra.adjoin (grading k 0) (Set.range (coordinate k))=⊤ := by
  have hpoly : ∀ p : Ring k,p∈Algebra.adjoin (grading k 0) (Set.range (coordinate k)) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact (Algebra.adjoin (grading k 0) (Set.range (coordinate k))).algebraMap_mem
        ⟨C a,isHomogeneous_C (Fin 2) a⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i,rfl⟩)
  apply top_unique
  intro p _
  exact hpoly p

theorem monomial_ratio (i : Fin 2) (a : ℕ) (ai : Fin 2 → ℕ)
    (hai : ∑j,ai j=a) (ha : (∏j,coordinate k j^ai j)∈grading k (a • (1:ℕ))) :
    HomogeneousLocalization.Away.mk (grading k) (coordinate_degree k i) a
      (∏j,coordinate k j^ai j) ha=∏j,ratio k i j^ai j := by
  apply HomogeneousLocalization.val_injective
  calc
    _=algebraMap (Ring k) (LocalizedRing k i) (∏j,coordinate k j^ai j)*
        inverseCoordinate k i^a := by
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
        IsLocalization.mk'_eq_mul_mk'_one]
      congr 1
      simp only [inverseCoordinate,IsLocalization.Away.invSelf,←IsLocalization.mk'_pow,one_pow]
      rfl
    _=_ := by
      change _=algebraMap (ChartRing k i) (LocalizedRing k i) (∏j,ratio k i j^ai j)
      rw [map_prod,map_prod]
      simp only [map_pow,HomogeneousLocalization.algebraMap_apply,ratio_val,mul_pow]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hai]

theorem chartAlgHom_ext {S : Type*} [CommRing S] [Algebra k S] (i : Fin 2)
    (f g : ChartRing k i →ₐ[k] S) (h : ∀j,f (ratio k i j)=g (ratio k i j)) : f=g := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
    (coordinate_degree k i) (coordinate k) (coordinate_adjoin k) (fun _ : Fin 2 => (1:ℕ))
    (fun j => coordinate_degree k j)
  apply AlgHom.ext
  intro x
  have hx : x∈Submodule.span (grading k 0)
      {HomogeneousLocalization.Away.mk (grading k) (coordinate_degree k i) a
        (∏j,coordinate k j^ai j) (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun j _ => coordinate_degree k j)) |
        (a : ℕ) (ai : Fin 2 → ℕ) (hai : ∑j,ai j • (1:ℕ)=a • (1:ℕ))} := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a,ai,hai,rfl⟩ := hy
    rw [monomial_ratio k i a ai (by simpa using hai)]
    simp only [map_prod,map_pow,h]
  | zero => simp
  | add x y hx hy hfx hfy => simp only [map_add,hfx,hfy]
  | smul r x hx hfx =>
    obtain ⟨a,rfl⟩ := degreeZero_eq_coefficient k r
    change f (algebraMap k (ChartRing k i) a*x)=g (algebraMap k (ChartRing k i) a*x)
    simp only [map_mul,AlgHom.commutes,hfx]

def chartInclusion (i : Fin 2) : Spec (CommRingCat.of (ChartRing k i)) ⟶ scheme k :=
  Proj.awayι (grading k) (coordinate k i) (coordinate_degree k i) (by decide : 0<1)

instance chartInclusion_openImmersion (i : Fin 2) : IsOpenImmersion (chartInclusion k i) := by
  dsimp only [chartInclusion]
  infer_instance

theorem coordinate_opens_cover :
    ⨆ i : Fin 2, Proj.basicOpen (grading k) (coordinate k i)=⊤ :=
  Proj.iSup_basicOpen_eq_top' (grading k) (coordinate k)
    (fun i=>⟨1,coordinate_degree k i⟩) (coordinate_adjoin k)

theorem chartInclusion_opensRange (i : Fin 2) :
    (chartInclusion k i).opensRange=Proj.basicOpen (grading k) (coordinate k i) :=
  Proj.opensRange_awayι _ _ _ _

theorem chartInclusion_structureMap (i : Fin 2) :
    chartInclusion k i ≫ structureMap k=
      Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing k i))) := by
  dsimp only [chartInclusion,structureMap,scheme,ProjFieldPoint.structureMap]
  rw [←Category.assoc,Proj.awayι_toSpecZero,←Spec.map_comp]
  rfl

end
end AlgebraicGeometry.ProjectiveLine.Charts
