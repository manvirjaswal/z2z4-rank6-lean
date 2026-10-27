module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Tactic

@[expose] public section

/-!
# Compatible chart sections and the intersection of their images

For two injective linear restrictions to a common overlap, the compatible
pairs form exactly the intersection of the two images. This is a general linear-algebra statement.
-/

namespace Z2Z4Rank6.TwoChartEqualizer
noncomputable section

variable {R A B C : Type*} [Field R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

def difference (f : A→ₗ[R]B) (g : C→ₗ[R]B) : (A×C)→ₗ[R]B :=
  f.comp (LinearMap.fst R A C)-g.comp (LinearMap.snd R A C)

@[simp] theorem mem_ker_difference (f : A→ₗ[R]B) (g : C→ₗ[R]B) (p : A×C) :
    p∈LinearMap.ker (difference f g)↔f p.1=g p.2 := by
  simp [difference,sub_eq_zero]

def toIntersection (f : A→ₗ[R]B) (g : C→ₗ[R]B) :
    LinearMap.ker (difference f g)→ₗ[R]↥(LinearMap.range f⊓LinearMap.range g) where
  toFun p := ⟨f p.1.1,⟨⟨p.1.1,rfl⟩,
    ⟨p.1.2,((mem_ker_difference f g p.1).mp p.2).symm⟩⟩⟩
  map_add' _ _ := Subtype.ext (map_add f _ _)
  map_smul' r _ := Subtype.ext (map_smul f r _)

theorem toIntersection_injective (f : A→ₗ[R]B) (g : C→ₗ[R]B)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (toIntersection f g) := by
  intro p q hpq
  apply Subtype.ext
  apply Prod.ext
  · exact hf (congrArg Subtype.val hpq)
  · apply hg
    have hp := (mem_ker_difference f g p.1).mp p.2
    have hq := (mem_ker_difference f g q.1).mp q.2
    exact hp.symm.trans ((congrArg Subtype.val hpq).trans hq)

theorem toIntersection_surjective (f : A→ₗ[R]B) (g : C→ₗ[R]B) :
    Function.Surjective (toIntersection f g) := by
  intro b
  obtain ⟨a,ha⟩ := b.2.1
  obtain ⟨c,hc⟩ := b.2.2
  refine ⟨⟨(a,c),(mem_ker_difference f g (a,c)).mpr (ha.trans hc.symm)⟩,?_⟩
  exact Subtype.ext ha

/-- The kernel of the restriction difference is linearly
equivalent to the intersection of the two restriction images. -/
def compatibleEquivIntersection (f : A→ₗ[R]B) (g : C→ₗ[R]B)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    LinearMap.ker (difference f g)≃ₗ[R]↥(LinearMap.range f⊓LinearMap.range g) :=
  LinearEquiv.ofBijective (toIntersection f g)
    ⟨toIntersection_injective f g hf hg,toIntersection_surjective f g⟩

end
end Z2Z4Rank6.TwoChartEqualizer
