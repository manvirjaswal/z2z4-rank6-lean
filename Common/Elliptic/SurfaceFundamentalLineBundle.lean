import Common.Elliptic.ComplexEllipticSurfaceTheorems
import Common.AlgebraicGeometry.CurveLineBundle
import Common.AlgebraicGeometry.HigherDirectImage

/-!
# The fundamental line bundle of a section

For a section s:C -> X the fundamental line bundle is its
conormal sheaf. Miranda Definition II.4.1 p. 23 defines L as the inverse
normal bundle of the section, pushed to C; the identification s(C)=C
makes this precisely s^*ker(O_X -> s_*O_C). Resolution of the associated
Weierstrass fibration preserves a neighbourhood of the section.

The input for III.4.4 p. 34 concerns the degree of this line bundle.
The input for Lemma III.4.6(a) p. 35 uses degree two, exactly as printed.
The deduction from Euler 24 is proved below.
-/
namespace Common.Elliptic.SurfaceFundamentalLineBundle
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SurfaceModel ComplexEllipticSurfaceTheorems
open Common.AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
variable {k : Type} [Field k] {W : WeierstrassCurve (RatFunc k)}
  (M : RegularModel k W) (s : ProjectiveLine.scheme k ⟶ M.scheme)

def sheaf : (ProjectiveLine.scheme k).Modules := ConormalDegree.conormal s

def degree : ℤ := CurveLineBundle.degree k (ProjectiveLine.scheme k)
  (ProjectiveLine.structureMap k) (sheaf M s)

/-- The section is a closed immersion; its ideal and conormal
are the closed-immersion ideal and conormal. -/
theorem section_closed (hs : s≫M.projection=𝟙 _) : IsClosedImmersion s := by
  let : IsClosedImmersion (s≫M.projection) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s M.projection

/-- The R^1 pi_*O, for comparison with Miranda II.3.6 and II.4.1. -/
def firstDirectImage : (ProjectiveLine.scheme k).Modules :=
  HigherDirectImage.structureSheaf M.projection 1

/-- Miranda formula III.4.4 p. 34, on a projective minimal
elliptic surface over P1_C with its section conormal line. -/
def MirandaIII44 : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W),
    M.IsRelativelyMinimal → ProjectiveScheme.IsProjective ℂ M.scheme M.structureMap →
    ∀ s : ProjectiveLine.scheme ℂ ⟶ M.scheme,s≫M.projection=𝟙 _ →
      ComplexPointsTopology.HasFiniteHomology ℂ M.scheme M.structureMap 4 →
      ComplexPointsTopology.euler ℂ M.scheme M.structureMap 4=12*degree M s

/-- The K3 clause of Miranda Lemma III.4.6(a), p. 35, with g=0 and
fundamental line degree 2. -/
def MirandaLemmaIII46a : Prop :=
  ∀ (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W),
    M.IsRelativelyMinimal → ProjectiveScheme.IsProjective ℂ M.scheme M.structureMap →
    ∀ s : ProjectiveLine.scheme ℂ ⟶ M.scheme,s≫M.projection=𝟙 _ → degree M s=2 →
      Common.AlgebraicGeometry.IsK3 ℂ M.scheme M.structureMap

theorem isK3_of_euler24 (hEuler : MirandaIII44) (hClass : MirandaLemmaIII46a)
    (W : WeierstrassCurve (RatFunc ℂ)) [W.IsElliptic] (M : RegularModel ℂ W)
    (hmin : M.IsRelativelyMinimal)
    (hproj : ProjectiveScheme.IsProjective ℂ M.scheme M.structureMap)
    (hs : M.HasSection)
    (hf : ComplexPointsTopology.HasFiniteHomology ℂ M.scheme M.structureMap 4)
    (he : ComplexPointsTopology.euler ℂ M.scheme M.structureMap 4=24) :
    Common.AlgebraicGeometry.IsK3 ℂ M.scheme M.structureMap := by
  obtain ⟨s,hs⟩ := hs
  have hdeg := hEuler W M hmin hproj s hs hf
  have hd : degree M s=2 := by linarith
  exact hClass W M hmin hproj s hs hd

end
end Common.Elliptic.SurfaceFundamentalLineBundle
