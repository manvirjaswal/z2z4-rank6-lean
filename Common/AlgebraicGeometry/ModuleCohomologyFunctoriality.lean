import Common.AlgebraicGeometry.ModuleCohomologyBaseChange

/-! Module-sheaf isomorphisms induce linear cohomology isomorphisms. -/
namespace Common.AlgebraicGeometry.ModuleSheafCohomology
noncomputable section
set_option maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open StructureSheafCohomology
variable (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k))

def coefficientFunctor : X.Modules ⥤ Sheaves k X :=
  SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op (⊤ : X.Opens))
    (isTerminalTop.op) ⋙
      sheafCompose (Opens.grothendieckTopology X)
        (ModuleCat.restrictScalars (scalarMap k X s))

def coefficientIso {M N : X.Modules} (e : M ≅ N) :
    coefficientSheaf k X s M ≅ coefficientSheaf k X s N :=
  (coefficientFunctor k X s).mapIso e

def cohomologyIso {M N : X.Modules} (e : M ≅ N) (i : ℕ) :
    Cohomology k X s M i ≃ₗ[k] Cohomology k X s N i where
  toFun a := a.comp (Abelian.Ext.mk₀ (coefficientIso k X s e).hom) (add_zero i)
  invFun a := a.comp (Abelian.Ext.mk₀ (coefficientIso k X s e).inv) (add_zero i)
  left_inv a := by
    dsimp only
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero,Abelian.Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id,Abelian.Ext.comp_mk₀_id]
  right_inv a := by
    dsimp only
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero,Abelian.Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id,Abelian.Ext.comp_mk₀_id]
  map_add' a b := Abelian.Ext.add_comp _ _ _ _
  map_smul' a b := Abelian.Ext.smul_comp _ _ _ _

theorem euler_eq_of_iso {M N : X.Modules} (e : M ≅ N) :
    euler01 k X s M=euler01 k X s N := by
  simp only [euler01,(cohomologyIso k X s e 0).finrank_eq,
    (cohomologyIso k X s e 1).finrank_eq]

end
end Common.AlgebraicGeometry.ModuleSheafCohomology

namespace Common.AlgebraicGeometry.ModuleCohomologyBaseChange
noncomputable section
set_option maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry CategoryTheory
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of k)}
  {t : Y ⟶ Spec (CommRingCat.of K)} {M : X.Modules} {N P : Y.Modules}

def Comparison.transportRight (e : Comparison k K X Y s t M N) (f : N ≅ P) :
    Comparison k K X Y s t M P where
  zero := e.zero.trans (ModuleSheafCohomology.cohomologyIso K Y t f 0)
  one := e.one.trans (ModuleSheafCohomology.cohomologyIso K Y t f 1)

end
end Common.AlgebraicGeometry.ModuleCohomologyBaseChange
