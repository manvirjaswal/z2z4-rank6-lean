import Z2Z4Rank6.StructureSheafCohomology
import Z2Z4Rank6.TwoChartEqualizer
import Mathlib.Topology.Sheaves.CommRingCat

/-! Two-open gluing for the rational structure sheaf.
Mathlib's ring-sheaf gluing isomorphism proves bijectivity; the forward map
uses the rational-linear restrictions, so it is rational-linear. -/
namespace Z2Z4Rank6.StructureSheafGlobalSections
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open StructureSheafCohomology

variable (X : Scheme.{0}) (s : X⟶Base) (U V : X.Opens)

abbrev Compatible := LinearMap.ker (TwoChartEqualizer.difference
  (restriction X s U (U⊓V) inf_le_left)
  (restriction X s V (U⊓V) inf_le_right))

abbrev RingCompatible := RingHom.eqLocus
  ((X.presheaf.map (homOfLE (inf_le_left : U⊓V≤U)).op).hom.comp
    (RingHom.fst (X.presheaf.obj (op U)) (X.presheaf.obj (op V))))
  ((X.presheaf.map (homOfLE (inf_le_right : U⊓V≤V)).op).hom.comp
    (RingHom.snd (X.presheaf.obj (op U)) (X.presheaf.obj (op V))))

def unionRestrictions : sectionModule X s (U⊔V)→ₗ[ℚ]
    (sectionModule X s U×sectionModule X s V) :=
  (restriction X s (U⊔V) U le_sup_left).prod
    (restriction X s (U⊔V) V le_sup_right)

theorem unionRestrictions_compatible (a : sectionModule X s (U⊔V)) :
    unionRestrictions X s U V a∈Compatible X s U V := by
  apply (TwoChartEqualizer.mem_ker_difference _ _ _).mpr
  have h := ((X.sheaf.objSupIsoProdEqLocus U V).hom a).property
  change (X.presheaf.map (homOfLE (inf_le_left : U⊓V≤U)).op)
      (((X.sheaf.objSupIsoProdEqLocus U V).hom a).val.1)=
    (X.presheaf.map (homOfLE (inf_le_right : U⊓V≤V)).op)
      (((X.sheaf.objSupIsoProdEqLocus U V).hom a).val.2) at h
  rw [TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst X.sheaf U V a,
    TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd X.sheaf U V a] at h
  exact h

def unionToCompatible : sectionModule X s (U⊔V)→ₗ[ℚ]Compatible X s U V :=
  (unionRestrictions X s U V).codRestrict (Compatible X s U V)
    (unionRestrictions_compatible X s U V)

theorem unionToCompatible_injective : Function.Injective (unionToCompatible X s U V) := by
  intro a b hab
  have hp := congrArg Subtype.val hab
  have hring : (X.sheaf.objSupIsoProdEqLocus U V).hom a=
      (X.sheaf.objSupIsoProdEqLocus U V).hom b := by
    apply Subtype.ext
    apply Prod.ext
    · rw [TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst X.sheaf U V a,
        TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst X.sheaf U V b]
      exact congrArg Prod.fst hp
    · rw [TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd X.sheaf U V a,
        TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd X.sheaf U V b]
      exact congrArg Prod.snd hp
  exact (ConcreteCategory.bijective_of_isIso (X.sheaf.objSupIsoProdEqLocus U V).hom).1 hring

def compatibleToRing (p : Compatible X s U V) : RingCompatible X U V := by
  refine ⟨p.val,?_⟩
  exact (TwoChartEqualizer.mem_ker_difference _ _ _).mp p.property

theorem unionToCompatible_surjective : Function.Surjective (unionToCompatible X s U V) := by
  intro p
  refine ⟨(X.sheaf.objSupIsoProdEqLocus U V).inv (compatibleToRing X s U V p),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (X.presheaf.map (homOfLE (le_sup_left : U≤U⊔V)).op)
      ((X.sheaf.objSupIsoProdEqLocus U V).inv (compatibleToRing X s U V p))=p.val.1
    exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst X.sheaf U V (compatibleToRing X s U V p)
  · change (X.presheaf.map (homOfLE (le_sup_right : V≤U⊔V)).op)
      ((X.sheaf.objSupIsoProdEqLocus U V).inv (compatibleToRing X s U V p))=p.val.2
    exact TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd X.sheaf U V (compatibleToRing X s U V p)

/-- Structure-sheaf sections on a union are exactly the compatible
pairs of rational-linear chart sections. -/
def unionEquivCompatible : sectionModule X s (U⊔V)≃ₗ[ℚ]Compatible X s U V :=
  LinearEquiv.ofBijective (unionToCompatible X s U V)
    ⟨unionToCompatible_injective X s U V,unionToCompatible_surjective X s U V⟩

@[simp] theorem unionEquivCompatible_fst (a : sectionModule X s (U⊔V)) :
    (unionEquivCompatible X s U V a).val.1=restriction X s (U⊔V) U le_sup_left a := rfl
@[simp] theorem unionEquivCompatible_snd (a : sectionModule X s (U⊔V)) :
    (unionEquivCompatible X s U V a).val.2=restriction X s (U⊔V) V le_sup_right a := rfl

/-- For a two-open cover, global sections are exactly the
compatible chart pairs. -/
def globalEquivCompatible (hcover : U⊔V=⊤) :
    sectionModule X s ⊤≃ₗ[ℚ]Compatible X s U V :=
  hcover ▸ unionEquivCompatible X s U V
end
end Z2Z4Rank6.StructureSheafGlobalSections
