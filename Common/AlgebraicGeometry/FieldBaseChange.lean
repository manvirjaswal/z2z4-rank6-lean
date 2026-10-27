import Common.AlgebraicGeometry.K3BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! Elementary consequences and composition of field pullbacks. -/
namespace Common.AlgebraicGeometry.K3BaseChange
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

instance extension_surjective : Surjective (extensionMap k K) where
  surj _ := ⟨Classical.choice inferInstance,Subsingleton.elim _ _⟩

instance extension_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (extensionMap k K) :=
  .of_isDominant _

variable {X Y : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of k)}
  {t : Y ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ X}

theorem integral_reflects (h : IsPullback p t s (extensionMap k K)) [IsIntegral Y] :
    IsIntegral X := by
  let : Surjective p := MorphismProperty.of_isPullback h.flip inferInstance
  let : QuasiCompact p := MorphismProperty.of_isPullback h.flip inferInstance
  let : IsSchemeTheoreticallyDominant p := .of_isPullback h.flip
  let : IsReduced X := IsSchemeTheoreticallyDominant.isReduced p
  let : IrreducibleSpace X := Function.Surjective.irreducibleSpace p.continuous p.surjective
  exact isIntegral_of_irreducibleSpace_of_isReduced X

variable (L : Type) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

theorem extensionMap_comp : extensionMap K L≫extensionMap k K=extensionMap k L := by
  unfold extensionMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact (IsScalarTower.algebraMap_apply k K L a).symm

variable (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))

def towerMap : scheme k L X s ⟶ scheme k K X s :=
  pullback.lift (pullback.fst s (extensionMap k L))
    (pullback.snd s (extensionMap k L)≫extensionMap K L) (by
      rw [Category.assoc,extensionMap_comp]
      exact pullback.condition)

@[reassoc (attr:=simp)] theorem towerMap_fst :
    towerMap k K L X s≫pullback.fst s (extensionMap k K)=
      pullback.fst s (extensionMap k L) := pullback.lift_fst _ _ _

@[reassoc (attr:=simp)] theorem towerMap_snd :
    towerMap k K L X s≫structureMap k K X s=
      structureMap k L X s≫extensionMap K L := pullback.lift_snd _ _ _

theorem towerMap_isPullback :
    IsPullback (towerMap k K L X s) (structureMap k L X s)
      (structureMap k K X s) (extensionMap K L) := by
  have h : IsPullback (pullback.fst s (extensionMap k L))
      (pullback.snd s (extensionMap k L)) s (extensionMap K L≫extensionMap k K) := by
    rw [extensionMap_comp k K L]
    exact .of_hasPullback _ _
  have hp := h.of_right' (IsPullback.of_hasPullback s (extensionMap k K))
  convert hp using 1 <;> first | rfl | (apply pullback.hom_ext <;> simp [towerMap])

variable {X} {s} {Y : Scheme.{0}} {t : Y ⟶ Spec (CommRingCat.of L)} {p : Y ⟶ X}

def intermediateMap (h : IsPullback p t s (extensionMap k L)) :
    Y ⟶ scheme k K X s :=
  pullback.lift p (t≫extensionMap K L) (by
    rw [Category.assoc,extensionMap_comp]
    exact h.w)

@[reassoc (attr:=simp)] theorem intermediateMap_fst
    (h : IsPullback p t s (extensionMap k L)) :
    intermediateMap k K L h≫pullback.fst s (extensionMap k K)=p :=
  pullback.lift_fst _ _ _

@[reassoc (attr:=simp)] theorem intermediateMap_snd
    (h : IsPullback p t s (extensionMap k L)) :
    intermediateMap k K L h≫structureMap k K X s=t≫extensionMap K L :=
  pullback.lift_snd _ _ _

theorem intermediateMap_isPullback (h : IsPullback p t s (extensionMap k L)) :
    IsPullback (intermediateMap k K L h) t (structureMap k K X s) (extensionMap K L) := by
  have h' : IsPullback p t s (extensionMap K L≫extensionMap k K) := by
    rw [extensionMap_comp]
    exact h
  have hp := h'.of_right' (IsPullback.of_hasPullback s (extensionMap k K))
  convert hp using 1 <;> first | rfl | (apply pullback.hom_ext <;> simp [intermediateMap])

end
end Common.AlgebraicGeometry.K3BaseChange
