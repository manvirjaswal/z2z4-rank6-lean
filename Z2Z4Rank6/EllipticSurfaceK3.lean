module

public import Z2Z4Rank6.EllipticSurfaceClassification
public import Common.Elliptic.EllipticSurfaceSections

@[expose] public section

/-!
# Full Lemma 3.1(b) from separately numbered model and section assertions

The model and generic-point/section correspondence are the separate
assertions of Gauthier Leterrier, Some Mordell-Weil lattices and
applications to sphere packings, EPFL thesis 10417 (2024), Remark 1.3.9,
p. 36. The source label is Remark, not Theorem. An infinity point
and the proved restriction map produce the section required by the
surface geometry argument. The other inputs and their references are in
EllipticSurfaceClassification.
-/
namespace Z2Z4Rank6.EllipticSurfaceK3
noncomputable section
open Common.AlgebraicGeometry Common.AlgebraicGeometry.K3BaseChange
open Common.Elliptic.SurfaceDescentSources
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open Common.Elliptic.SurfaceFundamentalLineBundle
open Common.Elliptic.EllipticSurfaceSections

theorem lemma_3_1_b (hModels : LeterrierRemark139Models ℚ)
    (hSections : LeterrierRemark139Sections ℚ) (H : PublishedInputs)
    (hLocal : MirandaTableIV31) (hEuler : SchuttShiodaSection67FiberEuler)
    (hSum : Common.Elliptic.SurfaceEulerCharacteristic.SchuttShiodaTheorem610)
    (hFundamentalEuler : MirandaIII44) (hClass : MirandaLemmaIII46a)
    (hCoh : Stacks02KHCartesianStructureSheaf ℚ ℂ)
    (hCotangent : CanonicalCotangentConstruction.StacksLemma29335 ℚ)
    (hExterior : CanonicalCotangentConstruction.StacksLemma2672)
    (hDifferentials : CanonicalBundleDescent.Stacks0FL5 ℚ ℂ)
    (hFinite : CanonicalBundleDescent.Stacks02O3Global ℚ)
    (hPicard : CanonicalBundleDescent.Stacks0CC5 ℚ ℂ) :
    EllipticSurfaceStatements.DiscriminantStatement ∧ EllipticSurfaceStatements.GeometryStatement :=
  EllipticSurfaceClassification.lemma_3_1_b
    hModels hSections H hLocal hEuler hSum hFundamentalEuler
    hClass hCoh hCotangent hExterior hDifferentials hFinite hPicard

end
end Z2Z4Rank6.EllipticSurfaceK3
