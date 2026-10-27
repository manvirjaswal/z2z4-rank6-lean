import Common.AlgebraicGeometry.ConormalDegree
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Exterior powers of module sheaves

Take the algebraic exterior power on each open, use the
semilinear restrictions, and sheafify. In particular the exterior powers
of the conormal of the diagonal define relative differential
forms.
The functorial construction follows Mathlib's presheaf tensor-product
pattern (Presheaf/Monoidal.lean), distributed under Apache 2.0.
-/
namespace Common.AlgebraicGeometry.ModuleExteriorPower
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

variable {A B : CommRingCat.{0}} (M : ModuleCat.{0} A) (N : ModuleCat.{0} B)
  (f : A ⟶ B) (g : M ⟶ (ModuleCat.restrictScalars f.hom).obj N) (d : ℕ)

def restriction : ModuleCat.of A (⋀[A]^d M) ⟶
    (ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B (⋀[B]^d N)) := by
  refine ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f.hom).obj
    (ModuleCat.of B (⋀[B]^d N))) ?_
  refine exteriorPower.alternatingMapLinearEquiv ?_
  refine { toFun := fun m=>exteriorPower.ιMulti B d (fun i=>g (m i))
           map_update_add' := ?_
           map_update_smul' := ?_
           map_eq_zero_of_eq' := ?_ }
  · intro _ m i x y
    change exteriorPower.ιMulti B d (g ∘ Function.update m i (x+y)) =
      exteriorPower.ιMulti B d (g ∘ Function.update m i x) +
        exteriorPower.ιMulti B d (g ∘ Function.update m i y)
    rw [Function.comp_update,Function.comp_update,Function.comp_update,map_add]
    exact (exteriorPower.ιMulti B d).map_update_add _ i _ _
  · intro _ m i a x
    change exteriorPower.ιMulti B d (g ∘ Function.update m i (a • x)) =
      (f a) • exteriorPower.ιMulti B d (g ∘ Function.update m i x)
    rw [Function.comp_update,Function.comp_update]
    have hg : g (a • x)=(f a) • g x := g.hom.map_smul a x
    rw [hg]
    exact (exteriorPower.ιMulti B d).map_update_smul _ i _ _
  · intro m i j hij hne
    exact (exteriorPower.ιMulti B d).map_eq_zero_of_eq _ (congrArg g hij) hne

@[simp] theorem restriction_wedge (m : Fin d → M) :
    DFunLike.coe (α := ModuleCat.of A (⋀[A]^d M))
      (β := fun _=>(ModuleCat.restrictScalars f.hom).obj (ModuleCat.of B (⋀[B]^d N)))
      (ModuleCat.Hom.hom (restriction M N f g d)) (exteriorPower.ιMulti A d m)=
      exteriorPower.ιMulti B d (fun i=>g (m i)) := by
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ m

variable {C : Type} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{0})
  (P : PresheafOfModulesOfCommRing.{0} R) (d : ℕ)

def presheafExterior : PresheafOfModulesOfCommRing.{0} R :=
  PresheafOfModulesOfCommRing.mk
    (fun U=>ModuleCat.of (R.obj U) (⋀[R.obj U]^d (P.obj U)))
    (fun f=>restriction _ _ (R.map f) (P.map f) d)
    (fun U=>by
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      ext m
      dsimp [restriction]
      simp
      rfl)
    (fun f g=>by
      apply ModuleCat.hom_ext
      apply exteriorPower.linearMap_ext
      ext m
      dsimp [restriction]
      simp)

variable (X : Scheme.{0}) (M : X.Modules) (d : ℕ)

def presheaf : X.PresheafOfModules := presheafExterior X.presheaf M.val d

def sheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (presheaf X M d)

variable (k : Type) [Field k] (s : X ⟶ Spec (CommRingCat.of k))

def differentialForms : X.Modules :=
  sheaf X (ConormalDegree.conormal (CategoryTheory.Limits.pullback.diagonal s)) d

end
end Common.AlgebraicGeometry.ModuleExteriorPower
