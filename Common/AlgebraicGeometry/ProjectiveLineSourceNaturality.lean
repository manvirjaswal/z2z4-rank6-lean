module

public import Common.AlgebraicGeometry.ProjectiveLinePointNaturality

@[expose] public section

/-! The projective-coordinate points commute with source-field maps. -/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial Charts
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]
variable {K L : Type} [Field K] [Field L] [Algebra k K] [Algebra k L]

theorem affinePoint_sourceMap (g : K →ₐ[k] L) (t : K) :
    Spec.map (CommRingCat.ofHom g.toRingHom)≫affinePoint k K t=affinePoint k L (g t) := by
  rw [affinePoint_eq_chart,affinePoint_eq_chart,←Category.assoc,←Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (g.comp (chartEvaluation 1 (MvPolynomial.aeval ![t,1])
      (by simp [coordinate]))).toRingHom=
    (chartEvaluation 1 (MvPolynomial.aeval ![g t,1]) (by simp [coordinate])).toRingHom
  apply congrArg AlgHom.toRingHom
  apply chartAlgHom_ext k 1
  intro j
  fin_cases j <;> simp [coordinate]

theorem infinityPoint_sourceMap (g : K →ₐ[k] L) :
    Spec.map (CommRingCat.ofHom g.toRingHom)≫infinityPoint k K=infinityPoint k L := by
  rw [infinityPoint_eq_chart,infinityPoint_eq_chart,←Category.assoc,←Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (g.comp (chartEvaluation 0 (MvPolynomial.aeval ![(1:K),0])
      (by simp [coordinate]))).toRingHom=
    (chartEvaluation 0 (MvPolynomial.aeval ![(1:L),0]) (by simp [coordinate])).toRingHom
  apply congrArg AlgHom.toRingHom
  apply chartAlgHom_ext k 0
  intro j
  fin_cases j <;> simp [coordinate]

end
end AlgebraicGeometry.ProjectiveLine
