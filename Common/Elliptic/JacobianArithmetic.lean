module

public import Common.Elliptic.WeierstrassGroupLaw
public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

@[expose] public section

/-!
# Arithmetic transport to a Jacobian

The bridge is an additive equivalence induced by a group-scheme
isomorphism. Consequently rank and the torsion subgroup transport.
-/
namespace WeierstrassScheme.RegularGroupLaw
noncomputable section
open AlgebraicGeometry CategoryTheory Jacobian RationalStructureSheafCohomology
variable {W : WeierstrassCurve ℚ} [W.IsElliptic] (L : RegularGroupLaw W)
variable (hCFS : GenusOneModelTheorem.CFSTheorem28iiDegreeOne)
variable (hRigidity : MilneCorollary22) {C : Over Base}
variable (P : Presentation C (Over.mk (structureMap W)))

include L hCFS hRigidity in
theorem jacobian_rank_eq (n : Cardinal) (h : Module.rank ℤ W.toAffine.Point=n) :
    Module.rank ℤ P.abelian.Points=n :=
  (L.jacobianPointEquiv hCFS hRigidity P).toIntLinearEquiv.rank_eq.trans h

def jacobianTorsionEquiv :
    AddCommGroup.torsion P.abelian.Points ≃+ AddCommGroup.torsion W.toAffine.Point := by
  let e := L.jacobianPointEquiv hCFS hRigidity P
  exact (e.addSubgroupMap _).trans (AddEquiv.addSubgroupCongr e.map_torsion)

include L hCFS hRigidity in
theorem jacobian_torsion {T : Type} [AddCommGroup T]
    (h : Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ T)) :
    Nonempty (AddCommGroup.torsion P.abelian.Points ≃+ T) := by
  obtain ⟨e⟩ := h
  exact ⟨(L.jacobianTorsionEquiv hCFS hRigidity P).trans e⟩

end
end WeierstrassScheme.RegularGroupLaw
