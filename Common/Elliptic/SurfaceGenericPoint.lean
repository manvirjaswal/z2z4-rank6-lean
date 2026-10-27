import Common.Elliptic.SurfaceConstantExtension
import Common.AlgebraicGeometry.ProjectiveLineSourceNaturality

/-! The chosen generic point commutes with constant coefficient extension. -/
namespace Common.Elliptic.SurfaceWeierstrassData
noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

@[simp] theorem constantExtension_X : constantExtension k K RatFunc.X=RatFunc.X := by
  change constantExtension k K (algebraMap k[X] (RatFunc k) Polynomial.X)=_
  rw [constantExtension_polynomial,Polynomial.map_X]
  rfl

@[simp] theorem constantExtension_scalar (a : k) :
    constantExtension k K (algebraMap k (RatFunc k) a)=algebraMap k (RatFunc K) a := by
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k),constantExtension_polynomial]
  simp only [Polynomial.algebraMap_apply,Polynomial.map_C,Algebra.algebraMap_self,RingHom.id_apply]
  change algebraMap K[X] (RatFunc K) (algebraMap K K[X] (algebraMap k K a))=_
  rw [←IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
  exact (IsScalarTower.algebraMap_apply k K (RatFunc K) a).symm

def constantExtensionAlgHom : RatFunc k →ₐ[k] RatFunc K where
  toRingHom := constantExtension k K
  commutes' := constantExtension_scalar k K

theorem genericPoint_commutes :
    ProjectiveLine.genericPoint K≫ProjectiveLine.coefficientMap k K=
      Spec.map (CommRingCat.ofHom (constantExtension k K))≫ProjectiveLine.genericPoint k := by
  change ProjectiveLine.affinePoint K (RatFunc K) RatFunc.X≫ProjectiveLine.coefficientMap k K=
    Spec.map (CommRingCat.ofHom (constantExtension k K))≫
      ProjectiveLine.affinePoint k (RatFunc k) RatFunc.X
  rw [ProjectiveLine.affinePoint_coefficientMap]
  change _=Spec.map (CommRingCat.ofHom (constantExtensionAlgHom k K).toRingHom)≫_
  rw [ProjectiveLine.affinePoint_sourceMap]
  simp only [constantExtensionAlgHom,AlgHom.coe_mk,constantExtension_X]

end
end Common.Elliptic.SurfaceWeierstrassData
