import Z2Z4Rank6.ProjectiveBaseSchemeSections
import Z2Z4Rank6.AffineCoverCohomology
import Z2Z4Rank6.AffineBaseCechCokernel
import Z2Z4Rank6.RestrictionRangeTransport

/-! H¹ of the projective base scheme is one-dimensional.
The hypothesis is the published affine-cover comparison. -/
namespace Z2Z4Rank6.ProjectiveBaseSchemeH1
noncomputable section
open AlgebraicGeometry CategoryTheory
open ProjectiveBaseScheme ProjectiveBaseSchemeSections
open StructureSheafCohomology AffineBaseFunctionFieldIso

theorem zOpen_isAffine : IsAffineOpen zOpen :=
  Proj.isAffineOpen_basicOpen grading z (coordinate_degree 3) (by decide : 0<1)
theorem mOpen_isAffine : IsAffineOpen mOpen :=
  Proj.isAffineOpen_basicOpen grading m (coordinate_degree 0) (by decide : 0<1)
theorem overlapOpen_isAffine : IsAffineOpen (zOpen⊓mOpen) := by
  rw [←overlapOpen_eq]
  exact Proj.isAffineOpen_basicOpen grading (z*m) overlap_degree (by decide : 0<2)

abbrev leftRestriction := restriction scheme structureMap zOpen (zOpen⊓mOpen) inf_le_left
abbrev rightRestriction := restriction scheme structureMap mOpen (zOpen⊓mOpen) inf_le_right

theorem leftRestriction_map_range :
    (LinearMap.range leftRestriction).map overlapSectionsEquiv.toLinearMap=
      LinearMap.range affineRestriction :=
  RestrictionRangeTransport.map_range_of_intertwining leftRestriction affineRestriction zSectionsEquiv overlapSectionsEquiv zRestriction_eq

theorem rightRestriction_map_range :
    (LinearMap.range rightRestriction).map overlapSectionsEquiv.toLinearMap=
      LinearMap.range infinityRestriction.toLinearMap :=
  RestrictionRangeTransport.map_range_of_intertwining rightRestriction infinityRestriction.toLinearMap mSectionsEquiv overlapSectionsEquiv mRestriction_eq

private theorem actualOverlapDifferential_range :
    LinearMap.range AffineBaseCechCokernel.overlapDifferential=
      LinearMap.range affineRestriction⊔LinearMap.range infinityRestriction.toLinearMap := by
  have he : AffineBaseCechCokernel.overlapDifferential=
      AffineCoverModuleQuotient.difference affineRestriction infinityRestriction.toLinearMap := by
    apply LinearMap.ext
    intro p
    simp [AffineBaseCechCokernel.overlapDifferential,TwoChartEqualizer.difference,
      AffineCoverModuleQuotient.difference,sub_eq_add_neg]
  rw [he,AffineCoverModuleQuotient.range_difference]

/-- The sheaf restriction cokernel is the already computed concrete
one-dimensional quotient. -/
def cechCokernelEquivQ : AffineCoverCohomology.Cokernel scheme structureMap zOpen mOpen≃ₗ[ℚ]ℚ :=
  (AffineCoverModuleQuotient.quotientTransport leftRestriction rightRestriction overlapSectionsEquiv
    (LinearMap.range affineRestriction) (LinearMap.range infinityRestriction.toLinearMap)
    leftRestriction_map_range rightRestriction_map_range).trans
      ((Submodule.quotEquivOfEq _ _ actualOverlapDifferential_range.symm).trans
        AffineBaseCechCokernel.overlapCokernelEquiv)

/-- Structure-sheaf H¹ of the projective intersection is Q, by the published affine-cover
comparison. -/
def h1EquivQ (h : AffineCoverStructureSheafCohomologyTheorem) :
    StructureSheafCohomology.H1 scheme structureMap≃ₗ[ℚ]ℚ :=
  (AffineCoverCohomology.comparisonEquiv h scheme structureMap zOpen mOpen
    zOpen_isAffine mOpen_isAffine overlapOpen_isAffine two_chart_cover).symm.trans cechCokernelEquivQ

theorem h1_finiteDimensional (h : AffineCoverStructureSheafCohomologyTheorem) :
    FiniteDimensional ℚ (StructureSheafCohomology.H1 scheme structureMap) :=
  Module.Finite.equiv (h1EquivQ h).symm

theorem h1_finrank (h : AffineCoverStructureSheafCohomologyTheorem) :
    Module.finrank ℚ (StructureSheafCohomology.H1 scheme structureMap)=1 := by
  simpa using (h1EquivQ h).finrank_eq
end
end Z2Z4Rank6.ProjectiveBaseSchemeH1
