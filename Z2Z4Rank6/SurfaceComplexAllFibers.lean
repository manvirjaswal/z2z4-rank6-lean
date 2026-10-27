import Z2Z4Rank6.SurfaceComplexGeometry
import Common.AlgebraicGeometry.ProjectiveLineAllPoints

/-! The geometric fiber list covers all linear complex base points. -/
namespace Z2Z4Rank6.SurfaceComplexGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open SurfaceBadParameters

def fiberAt (M : Model) (p : Spec (CommRingCat.of ℂ) ⟶ ProjectiveLine.scheme ℂ) :
    Over (Spec (CommRingCat.of ℂ)) := Over.mk (M.fiberStructureMap p)

/-- Every geometric fiber is one of the nine polygons or a
smooth elliptic cubic. The base-point linearity condition is explicit. -/
theorem all_geometric_fibers (hLocal : MirandaTableIV31) (M : Model)
    (hmin : M.IsRelativelyMinimal) (hs : M.HasSection)
    (p : Spec (CommRingCat.of ℂ) ⟶ ProjectiveLine.scheme ℂ)
    (hp : p≫ProjectiveLine.structureMap ℂ=𝟙 _) :
    (∃ i : Fin 9,p=parameterPoint (parameter i) ∧
      Common.Elliptic.NeronPolygon.IsTypeI ℂ (fiberAt M p) (order i)) ∨
      IsGoodFiber (fiberAt M p) := by
  obtain ⟨t,ht⟩ := ProjectiveLine.parameterPoint_surjective ℂ p hp
  have hparam : ProjectiveLine.parameterPoint ℂ t=parameterPoint t := by cases t <;> rfl
  rw [hparam] at ht
  subst p
  by_cases h : t∈support
  · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
    subst t
    exact Or.inl ⟨i,rfl,fiber_types hLocal M hmin hs i⟩
  · exact Or.inr (good_elsewhere hLocal M hmin hs t h)

end
end Z2Z4Rank6.SurfaceComplexGeometry
