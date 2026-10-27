import Common.Elliptic.SurfaceGenericPoint
import Common.AlgebraicGeometry.FieldBaseChange

/-! Constant extension of generic equations commutes with towers. -/
namespace Common.Elliptic.SurfaceWeierstrassData
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
variable (k K L : Type) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]

theorem constantExtension_comp :
    (constantExtension K L).comp (constantExtension k K)=constantExtension k L := by
  apply IsFractionRing.ringHom_ext (A:=k[X])
  intro p
  simp only [RingHom.comp_apply,constantExtension_polynomial,Polynomial.map_map]
  congr 2
  exact (IsScalarTower.algebraMap_eq k K L).symm

theorem curve_constantExtension_comp (W : WeierstrassCurve (RatFunc k)) :
    (W.map (constantExtension k K)).map (constantExtension K L)=
      W.map (constantExtension k L) := by
  rw [WeierstrassCurve.map_map,constantExtension_comp]

end
end Common.Elliptic.SurfaceWeierstrassData
