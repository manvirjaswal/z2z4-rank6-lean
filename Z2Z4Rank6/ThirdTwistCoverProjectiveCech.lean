module

public import Z2Z4Rank6.ThirdTwistCoverProjectiveSections
public import Z2Z4Rank6.AffineCoverCohomology
public import Z2Z4Rank6.ThirdTwistCoverCechAlgebra
public import Z2Z4Rank6.RestrictionRangeTransport

@[expose] public section

/-! Affine cover and its restriction cokernel. -/
namespace Z2Z4Rank6.ThirdTwistCoverProjectiveH1
noncomputable section
open AlgebraicGeometry CategoryTheory
open ThirdTwistCoverProjective ThirdTwistCoverProjectiveSections
open StructureSheafCohomology ThirdTwistCoverOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem zOpen_isAffine : IsAffineOpen (zOpen) :=
  Proj.isAffineOpen_basicOpen (grading) (z) (coordinate_degree 3) (by decide : 0<1)
theorem mOpen_isAffine : IsAffineOpen (mOpen) :=
  Proj.isAffineOpen_basicOpen (grading) (m) (coordinate_degree 0) (by decide : 0<1)
theorem overlapOpen_isAffine : IsAffineOpen ((zOpen)⊓(mOpen)) := by
  rw [←overlapOpen_eq]
  exact Proj.isAffineOpen_basicOpen (grading) ((z)*(m)) (overlap_degree) (by decide : 0<2)

abbrev leftRestriction := restriction (scheme) (structureMap) (zOpen) ((zOpen)⊓(mOpen)) inf_le_left
abbrev rightRestriction := restriction (scheme) (structureMap) (mOpen) ((zOpen)⊓(mOpen)) inf_le_right

theorem leftRestriction_map_range :
    (LinearMap.range (leftRestriction)).map (overlapSectionsEquiv).toLinearMap=
      LinearMap.range (affineRestriction) :=
  RestrictionRangeTransport.map_range_of_intertwining (leftRestriction) (affineRestriction)
    (zSectionsEquiv) (overlapSectionsEquiv) (zRestriction_eq)

theorem rightRestriction_map_range :
    (LinearMap.range (rightRestriction)).map (overlapSectionsEquiv).toLinearMap=
      LinearMap.range (infinityRestriction).toLinearMap :=
  RestrictionRangeTransport.map_range_of_intertwining (rightRestriction) (infinityRestriction).toLinearMap
    (mSectionsEquiv) (overlapSectionsEquiv) (mRestriction_eq)

def cechCokernelEquiv :
    AffineCoverCohomology.Cokernel (scheme) (structureMap) (zOpen) (mOpen)≃ₗ[ℚ](Fin 5→ℚ) :=
  (AffineCoverModuleQuotient.quotientTransport (leftRestriction) (rightRestriction)
    (overlapSectionsEquiv) (LinearMap.range (affineRestriction))
    (LinearMap.range (infinityRestriction).toLinearMap)
    (leftRestriction_map_range) (rightRestriction_map_range)).trans
      ((Submodule.quotEquivOfEq _ _ (ThirdTwistCoverCechAlgebra.overlapDifferential_range).symm).trans
        (ThirdTwistCoverCechAlgebra.overlapCokernelEquiv))

end
end Z2Z4Rank6.ThirdTwistCoverProjectiveH1
