import Common.AlgebraicGeometry.ProjectiveLineBaseChangeCharts
import Common.AlgebraicGeometry.ProjValuedPointCharts

/-! Finite and infinity points commute with coefficient extension. -/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial Charts
set_option backward.isDefEq.respectTransparency false
variable (k K : Type) [Field k] [Field K] [Algebra k K]

theorem affinePoint_eq_chart (t : K) : affinePoint k K t=
    Spec.map (CommRingCat.ofHom (chartEvaluation 1 (MvPolynomial.aeval ![t,1])
      (by simp [coordinate])).toRingHom)≫chartInclusion k 1 := by
  rw [affinePoint,ProjValuedPoint.point_eq_chart]
  rfl

theorem infinityPoint_eq_chart : infinityPoint k K=
    Spec.map (CommRingCat.ofHom (chartEvaluation 0 (MvPolynomial.aeval ![(1:K),0])
      (by simp [coordinate])).toRingHom)≫chartInclusion k 0 := by
  rw [infinityPoint,ProjValuedPoint.point_eq_chart]
  rfl

variable {L : Type} [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]

def chartCoefficientEvaluation (i : Fin 2) (e : Ring K →ₐ[K] L)
    (he : e (coordinate K i)=1) : ChartRing k i →ₐ[k] L where
  toRingHom := (chartEvaluation i e he).toRingHom.comp (chartCoefficientHom k K i)
  commutes' a := by
    change chartEvaluation i e he
      (chartCoefficientHom k K i (algebraMap k (ChartRing k i) a))=algebraMap k L a
    rw [chartCoefficientHom_scalar,AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply k K L a).symm

theorem affinePoint_coefficientMap (t : L) :
    affinePoint K L t≫coefficientMap k K=affinePoint k L t := by
  rw [affinePoint_eq_chart,affinePoint_eq_chart,Category.assoc,chartInclusion_coefficientMap,
    ←Category.assoc,←Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (chartCoefficientEvaluation k K 1 (MvPolynomial.aeval ![t,1])
      (by simp [coordinate])).toRingHom=
    (chartEvaluation 1 (MvPolynomial.aeval ![t,1]) (by simp [coordinate])).toRingHom
  apply congrArg AlgHom.toRingHom
  apply chartAlgHom_ext k 1
  intro j
  simp [chartCoefficientEvaluation,coordinate]

theorem infinityPoint_coefficientMap :
    infinityPoint K L≫coefficientMap k K=infinityPoint k L := by
  rw [infinityPoint_eq_chart,infinityPoint_eq_chart,Category.assoc,chartInclusion_coefficientMap,
    ←Category.assoc,←Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (chartCoefficientEvaluation k K 0 (MvPolynomial.aeval ![(1:L),0])
      (by simp [coordinate])).toRingHom=
    (chartEvaluation 0 (MvPolynomial.aeval ![(1:L),0]) (by simp [coordinate])).toRingHom
  apply congrArg AlgHom.toRingHom
  apply chartAlgHom_ext k 0
  intro j
  simp [chartCoefficientEvaluation,coordinate]

end
end AlgebraicGeometry.ProjectiveLine
