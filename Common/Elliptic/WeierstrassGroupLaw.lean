module

public import Common.Elliptic.WeierstrassSchemeRationalPoints
public import Common.Elliptic.GenusOneModelTheorem
public import Common.AlgebraicGeometry.AbelianVarietyRigidity

@[expose] public section

/-!
# The regular group law on a Weierstrass cubic

Source: J. S. Milne, Elliptic Curves, second edition,
Proposition I.4.10 and Remark I.4.11(b,c), pp. 32–33, together with the
Weierstrass addition formulas of II.2, pp. 49–53:
https://www.jmilne.org/math/Books/EC2.pdf.

The input below is the group-object formulation of the source's assertion
that the usual chord-and-tangent group law is regular, specialized to Q.
Compatibility refers to canonical coordinate evaluations and Mathlib's
usual Weierstrass addition. Bijectivity of those evaluations is proved separately by charts.
Properness, smoothness and geometric connectedness are obtained from the CFS nonsingularity
criterion.
-/
namespace WeierstrassScheme
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Jacobian RationalStructureSheafCohomology
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false

local instance groupOverCartesian : CartesianMonoidalCategory (Over Base) :=
  Over.cartesianMonoidalCategory Base
local instance groupOverBraided : BraidedCategory (Over Base) := Over.braidedCategory Base

def rationalSection (W : WeierstrassCurve ℚ) (P : W.toAffine.Point) :
    𝟙_ (Over Base) ⟶ Over.mk (structureMap W) :=
  Over.homMk (RationalPoints.pointMorphism W P) (RationalPoints.pointMorphism_over W P)

def rationalSectionEquiv (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    W.toAffine.Point ≃ (𝟙_ (Over Base) ⟶ Over.mk (structureMap W)) :=
  Equiv.ofBijective (rationalSection W) (by
    constructor
    · intro P Q h
      exact RationalPoints.pointMorphism_injective W (congrArg (fun f=>f.left) h)
    · intro q
      obtain ⟨P,hP⟩ := RationalPoints.pointMorphism_surjective W q.left
      exact ⟨P,Over.OverMorphism.ext hP⟩)

/-- A regular group law on the cubic, with its usual evaluated addition. -/
structure RegularGroupLaw (W : WeierstrassCurve ℚ) [W.IsElliptic] where
  group : CommGrp (Over Base)
  carrierIso : Over.mk (structureMap W) ≅ group.X
  add_compat : ∀ P Q : W.toAffine.Point,
    rationalSection W (P+Q) ≫ carrierIso.hom =
      (rationalSection W P ≫ carrierIso.hom)*(rationalSection W Q ≫ carrierIso.hom)

/-- Milne's regular chord-and-tangent group law, in group-object notation. -/
def MilneRegularGroupLaw : Prop :=
  ∀ (W : WeierstrassCurve ℚ) [W.IsElliptic], Nonempty (RegularGroupLaw W)

namespace RegularGroupLaw
variable {W : WeierstrassCurve ℚ} [W.IsElliptic]

/-- The evaluated group law uses every rational section exactly once. -/
def pointEquiv (L : RegularGroupLaw W) :
    W.toAffine.Point ≃+ Additive (𝟙_ (Over Base) ⟶ L.group.X) where
  toEquiv :=
    (rationalSectionEquiv W).trans
      { toFun := fun p=>Additive.ofMul (p≫L.carrierIso.hom)
        invFun := fun p=>p.toMul≫L.carrierIso.inv
        left_inv := by intro p; simp
        right_inv := by intro p; simp }
  map_add' P Q := L.add_compat P Q

/-- The regular group scheme is an abelian variety. -/
def abelian (L : RegularGroupLaw W) (hCFS : GenusOneModelTheorem.CFSTheorem28iiDegreeOne) :
    AbelianVariety Base := by
  have hg := GenusOneModelTheorem.weierstrass_genus_one hCFS W W.Δ'.ne_zero
  let : IsProper (structureMap W) := hg.proper
  let : SmoothOfRelativeDimension 1 (structureMap W) := hg.smooth
  let : Smooth (structureMap W) := SmoothOfRelativeDimension.smooth 1 _
  let : GeometricallyIntegral (structureMap W) := hg.geometricallyIntegral
  let : GeometricallyConnected (structureMap W) := ⟨by
    intro K _ y Z fst snd h
    let : IsIntegral Z := GeometricallyIntegral.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have he : L.group.X.hom=L.carrierIso.inv.left≫structureMap W := L.carrierIso.inv.w.symm
  refine ⟨L.group,?_,?_,?_⟩
  · rw [he]; infer_instance
  · rw [he]; infer_instance
  · rw [he]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
      L.carrierIso.inv.left (structureMap W)).mpr inferInstance

/-- A Jacobian presentation has the point group of the printed cubic.
The source is a group-scheme isomorphism obtained using rigidity. -/
def jacobianPointEquiv (L : RegularGroupLaw W)
    (hCFS : GenusOneModelTheorem.CFSTheorem28iiDegreeOne)
    (hRigidity : MilneCorollary22) {C : Over Base}
    (P : Presentation C (Over.mk (structureMap W))) :
    P.abelian.Points ≃+ W.toAffine.Point :=
  (AbelianVariety.pointsEquiv (groupIsoOfSchemeIso hRigidity P.abelian (L.abelian hCFS)
    (P.carrierIso.symm ≪≫ L.carrierIso))).trans L.pointEquiv.symm

end RegularGroupLaw
end
end WeierstrassScheme
