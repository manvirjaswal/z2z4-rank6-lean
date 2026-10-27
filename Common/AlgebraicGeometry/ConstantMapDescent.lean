module

public import Common.AlgebraicGeometry.FieldBaseChange
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

@[expose] public section

/-!
# Constant morphisms descend along field extension

A rational point on the source supplies the value of the descended
constant map. Equality is reflected by the faithfully flat
projection, which is an epimorphism. Over an algebraically closed field
a nonempty locally finite-type source has such a point, by Mathlib's
closed-point correspondence.
-/
namespace Common.AlgebraicGeometry.ConstantMapDescent
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open K3BaseChange
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

variable {C D B : Scheme.{0}} {s : C ⟶ Spec (CommRingCat.of k)}
  {t : D ⟶ Spec (CommRingCat.of K)} {q : D ⟶ C}

theorem constant_descends_of_point (hp : IsPullback q t s (extensionMap k K))
    (a : Spec (CommRingCat.of k) ⟶ C) (ha : a≫s=𝟙 _) (f : C ⟶ B)
    (b : Spec (CommRingCat.of K) ⟶ B) (hf : q≫f=t≫b) : f=s≫(a≫f) := by
  let : Flat q := MorphismProperty.of_isPullback hp.flip inferInstance
  let : Surjective q := MorphismProperty.of_isPullback hp.flip inferInstance
  let : Epi q := Flat.epi_of_flat_of_surjective q
  let d : Spec (CommRingCat.of K) ⟶ D := hp.lift (extensionMap k K≫a) (𝟙 _) (by
    simp [Category.assoc,ha])
  have hb : extensionMap k K≫(a≫f)=b := by
    calc
      _=(d≫q)≫f := by simp [d,Category.assoc]
      _=d≫(q≫f) := Category.assoc _ _ _
      _=d≫(t≫b) := by rw [hf]
      _=b := by simp [d,←Category.assoc]
  apply (cancel_epi q).mp
  calc
    q≫f=t≫b := hf
    _=t≫(extensionMap k K≫(a≫f)) := by rw [hb]
    _=q≫(s≫(a≫f)) := by rw [←Category.assoc,←hp.w,Category.assoc]

variable [IsAlgClosed k]

theorem point_exists (C : Scheme.{0}) (s : C ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType s] [Nonempty C] :
    ∃ a : Spec (CommRingCat.of k) ⟶ C,a≫s=𝟙 _ := by
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨x,_,hx⟩ := nonempty_inter_closedPoints (X:=C)
    (Z:=Set.univ) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint s x hx,pointOfClosedPoint_comp s x hx⟩

end
end Common.AlgebraicGeometry.ConstantMapDescent
