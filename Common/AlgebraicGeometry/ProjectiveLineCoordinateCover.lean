import Common.AlgebraicGeometry.ProjectiveLineCharts

/-! The two-chart affine open cover of P1. -/
namespace AlgebraicGeometry.ProjectiveLine.Charts
noncomputable section
open CategoryTheory
variable (k : Type) [Field k]

def coordinateCover : (scheme k).AffineOpenCover where
  I₀ := Fin 2
  X i := CommRingCat.of (ChartRing k i)
  f i := chartInclusion k i
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    ((coordinate_opens_cover k).ge (show x∈(⊤ : (scheme k).Opens) from trivial))).choose
  covers x := by
    change x∈(chartInclusion k _).opensRange
    rw [chartInclusion_opensRange]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      ((coordinate_opens_cover k).ge (show x∈(⊤ : (scheme k).Opens) from trivial))).choose_spec

@[simp] theorem coordinateCover_f (i : Fin 2) :
    (coordinateCover k).f i=chartInclusion k i := rfl

end
end AlgebraicGeometry.ProjectiveLine.Charts
