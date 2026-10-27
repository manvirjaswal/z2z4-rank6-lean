import Z2Z4Rank6.GTorsionCoverProjectiveSections
import Z2Z4Rank6.AffineCoverCohomology
import Z2Z4Rank6.GTorsionCoverCechAlgebra
import Z2Z4Rank6.RestrictionRangeTransport

/-! Affine cover and its restriction cokernel. -/
namespace Z2Z4Rank6.GTorsionCoverProjectiveH1
noncomputable section
open AlgebraicGeometry CategoryTheory
open GTorsionCoverProjective GTorsionCoverProjectiveSections
open StructureSheafCohomology GTorsionCoverOverlap
variable (ε : Bool)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem zOpen_isAffine : IsAffineOpen (zOpen ε) :=
  Proj.isAffineOpen_basicOpen (grading ε) (z ε) (coordinate_degree ε 2) (by decide : 0<1)
theorem mOpen_isAffine : IsAffineOpen (mOpen ε) :=
  Proj.isAffineOpen_basicOpen (grading ε) (m ε) (coordinate_degree ε 0) (by decide : 0<1)
theorem overlapOpen_isAffine : IsAffineOpen ((zOpen ε)⊓(mOpen ε)) := by
  rw [←overlapOpen_eq]
  exact Proj.isAffineOpen_basicOpen (grading ε) ((z ε)*(m ε)) (overlap_degree ε) (by decide : 0<2)

abbrev leftRestriction := restriction (scheme ε) (structureMap ε) (zOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_left
abbrev rightRestriction := restriction (scheme ε) (structureMap ε) (mOpen ε) ((zOpen ε)⊓(mOpen ε)) inf_le_right

theorem leftRestriction_map_range :
    (LinearMap.range (leftRestriction ε)).map (overlapSectionsEquiv ε).toLinearMap=
      LinearMap.range (affineRestriction ε) :=
  RestrictionRangeTransport.map_range_of_intertwining (leftRestriction ε) (affineRestriction ε)
    (zSectionsEquiv ε) (overlapSectionsEquiv ε) (zRestriction_eq ε)

theorem rightRestriction_map_range :
    (LinearMap.range (rightRestriction ε)).map (overlapSectionsEquiv ε).toLinearMap=
      LinearMap.range (infinityRestriction ε).toLinearMap :=
  RestrictionRangeTransport.map_range_of_intertwining (rightRestriction ε) (infinityRestriction ε).toLinearMap
    (mSectionsEquiv ε) (overlapSectionsEquiv ε) (mRestriction_eq ε)

def cechCokernelEquiv :
    AffineCoverCohomology.Cokernel (scheme ε) (structureMap ε) (zOpen ε) (mOpen ε)≃ₗ[ℚ](Fin 9→ℚ) :=
  (AffineCoverModuleQuotient.quotientTransport (leftRestriction ε) (rightRestriction ε)
    (overlapSectionsEquiv ε) (LinearMap.range (affineRestriction ε))
    (LinearMap.range (infinityRestriction ε).toLinearMap)
    (leftRestriction_map_range ε) (rightRestriction_map_range ε)).trans
      ((Submodule.quotEquivOfEq _ _ (GTorsionCoverCechAlgebra.overlapDifferential_range ε).symm).trans
        (GTorsionCoverCechAlgebra.overlapCokernelEquiv ε))

end
end Z2Z4Rank6.GTorsionCoverProjectiveH1
