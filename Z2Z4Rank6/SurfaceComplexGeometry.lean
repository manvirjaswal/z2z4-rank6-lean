import Z2Z4Rank6.SurfaceBadParameters

/-!
# The complex minimal elliptic K3 surface of Lemma 3.1(b)

The generic curve is the printed equation over C(n). The total space is
a regular proper model over the projective line, with a
generic-fiber isomorphism. Every listed fiber is a Neron
polygon. Euler numbers use singular homology; K3 means
canonical triviality and H1 vanishing. The hypotheses are the published model-existence,
local-classification, Euler and K3 statements. Descent to the rational model is a separate
statement.
-/
namespace Z2Z4Rank6.SurfaceComplexGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.Elliptic.SurfaceModel Common.Elliptic.ComplexEllipticSurfaceTheorems
open SurfaceComplexData SurfaceBadParameters SurfaceLocalInvariants SurfaceWeierstrassCharts

abbrev Model := RegularModel ℂ curve

variable (hLocal : MirandaTableIV31) (M : Model)
variable (hmin : M.IsRelativelyMinimal) (hs : M.HasSection)

include hLocal hmin hs in
theorem fiber_types (i : Fin 9) :
    Common.Elliptic.NeronPolygon.IsTypeI ℂ (fiberOver M (parameter i)) (order i) := by
  fin_cases i
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 0)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 1)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 2)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 3)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 4)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_rational_bad (K:=ℂ) 5)
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_quadratic_root (quadraticRoot 0) (quadraticRoot_root 0))
  · exact hLocal.finite_multiplicative finiteEquation M hmin hs _ _
      (affine_multiplicativeData_at_quadratic_root (quadraticRoot 1) (quadraticRoot_root 1))
  · exact hLocal.infinity_multiplicative finiteEquation infinityEquation 2
      reciprocal_compatibility M hmin hs 1 (infinity_multiplicativeData (K:=ℂ))

include hLocal hmin hs in
theorem good_elsewhere (t : Option ℂ) (ht : t∉support) : IsGoodFiber (fiberOver M t) := by
  cases t with
  | none=>exact False.elim (ht none_mem_support)
  | some z=>
    apply hLocal.finite_good finiteEquation M hmin hs z
    apply affine_goodData_elsewhere z
    · intro i he
      apply ht
      rw [he]
      exact rational_mem_support i
    · intro hz
      obtain ⟨i,hi⟩ := (quadraticRoot_complete z).mp hz
      apply ht
      rw [←hi]
      exact quadratic_mem_support i

include hLocal hmin hs in
theorem local_euler_numbers (hEuler : SchuttShiodaSection67FiberEuler) (i : Fin 9) :
    ComplexPointsTopology.HasFiniteHomology ℂ
      (fiberOver M (parameter i)).left (fiberOver M (parameter i)).hom 2 ∧
    ComplexPointsTopology.euler ℂ
      (fiberOver M (parameter i)).left (fiberOver M (parameter i)).hom 2=(order i : ℤ) :=
  fiberEuler_eq hEuler curve M hmin hs (parameter i) (order i) (fiber_types hLocal M hmin hs i)


end
end Z2Z4Rank6.SurfaceComplexGeometry
