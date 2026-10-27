module

public import Z2Z4Rank6.SurfaceInvolutionGeneric
public import Z2Z4Rank6.SurfaceInvolutionBaseAction
public import Z2Z4Rank6.EllipticSurfaceK3
public import Common.AlgebraicGeometry.SurfaceModelAutomorphism

@[expose] public section

/-!
# The surface automorphism in Lemma 3.1(c)

The coefficient identities induce a semilinear isomorphism of the
complete generic cubic. Reprojection by the P1 involution preserves
the minimal regular projective model. The uniqueness clause of
Leterrier, Remark 1.3.9, printed p. 36, then supplies a scheme
automorphism of that surface, commuting with the printed base involution.
The final theorem retains the complete relatively minimal elliptic K3
context of Lemma 3.1(b), using the same published geometry inputs.
-/
namespace Z2Z4Rank6.SurfaceInvolution
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.AlgebraicGeometry Common.AlgebraicGeometry.K3BaseChange
open Common.AlgebraicGeometry.SurfaceModelAutomorphism
open Common.Elliptic.SurfaceModel Common.Elliptic.SurfaceDescentSources
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open Common.Elliptic.SurfaceFundamentalLineBundle
open Common.Elliptic.EllipticSurfaceSections
set_option backward.isDefEq.respectTransparency false

/-- The three automorphisms and their proved base squares. -/
def compatibleAutomorphisms : CompatibleAutomorphisms W where
  base := baseInvolution
  field := genericBaseInvolution
  curve := genericInvolution
  base_over := baseInvolution_over
  generic_base := genericBaseInvolution_over
  curve_over := genericInvolution_over

/-- An automorphism of the complete surface over Q which lies over
n↦9801/n on the projective line. -/
def LiftStatement (M : RegularModel ℚ W) : Prop :=
  ∃ f : M.scheme ≅ M.scheme,
    f.hom≫M.projection=M.projection≫baseInvolution.hom ∧
    f.hom≫M.structureMap=M.structureMap

/-- Lemma 3.1(c), including the surface automorphism. This holds for
any relatively minimal projective model of the printed generic cubic. -/
theorem lemma_3_1_c (hUnique : LeterrierRemark139Uniqueness ℚ)
    (M : RegularModel ℚ W) (hm : M.IsRelativelyMinimal) (hs : M.HasSection)
    (hp : ProjectiveScheme.IsProjective ℚ M.scheme M.structureMap) :
    (∀ n : F, n≠0 → surfaceS (9801/n)=(99/n)^4*surfaceS n) ∧
    (∀ n : F, n≠0 → surfaceW (9801/n)=(99/n)^4*surfaceW n) ∧
    LiftStatement M := by
  refine ⟨fun n hn=>surfaceS_involution n hn,fun n hn=>surfaceW_involution n hn,?_⟩
  obtain ⟨f,hf⟩ := automorphism_of_unique_model hUnique
    SurfaceRationalData.curveElliptic M hm hs hp compatibleAutomorphisms
  change f.hom≫M.projection=M.projection≫baseInvolution.hom at hf
  refine ⟨f,hf,?_⟩
  change f.hom≫(M.projection≫ProjectiveLine.structureMap ℚ)=_
  rw [←Category.assoc,hf,Category.assoc,baseInvolution_over]
  rfl

/-- The same complete relatively minimal elliptic K3 surface carries the
lift. The model, section and uniqueness inputs are the separate
clauses of Leterrier Remark 1.3.9; all remaining inputs are those of
EllipticSurfaceK3.lemma_3_1_b. -/
theorem complete_k3_surface_automorphism (hModels : LeterrierRemark139Models ℚ)
    (hSections : LeterrierRemark139Sections ℚ)
    (hUnique : LeterrierRemark139Uniqueness ℚ) (H : PublishedInputs)
    (hLocal : MirandaTableIV31) (hEuler : SchuttShiodaSection67FiberEuler)
    (hSum : Common.Elliptic.SurfaceEulerCharacteristic.SchuttShiodaTheorem610)
    (hFundamentalEuler : MirandaIII44) (hClass : MirandaLemmaIII46a)
    (hCoh : Stacks02KHCartesianStructureSheaf ℚ ℂ)
    (hCotangent : CanonicalCotangentConstruction.StacksLemma29335 ℚ)
    (hExterior : CanonicalCotangentConstruction.StacksLemma2672)
    (hDifferentials : CanonicalBundleDescent.Stacks0FL5 ℚ ℂ)
    (hFinite : CanonicalBundleDescent.Stacks02O3Global ℚ)
    (hPicard : CanonicalBundleDescent.Stacks0CC5 ℚ ℂ) :
    ∃ M : RegularModel ℚ W, M.IsRelativelyMinimal ∧ M.HasSection ∧
      ProjectiveScheme.IsProjective ℚ M.scheme M.structureMap ∧
      IsK3 ℚ M.scheme M.structureMap ∧ LiftStatement M := by
  obtain ⟨M,hm,hs,hp⟩ := (model_with_section ℚ hModels hSections) W
    SurfaceRationalData.curveElliptic
  let MC := SurfaceRationalDescent.complexModel H M
  have hmc := SurfaceRationalDescent.complexModel_isRelativelyMinimal H M hm hs hp
  have hsc := SurfaceRationalDescent.complexModel_hasSection H M hs
  have hpb := SurfaceRationalDescent.complexModel_isPullback H M
  have hpc := H.projective_baseChange ℚ ℂ M.scheme MC.scheme M.structureMap MC.structureMap
    (SurfaceRationalDescent.complexCoefficientMap H M) hpb hp
  obtain ⟨hf,he⟩ := EllipticSurfaceClassification.euler_eq_24 hLocal MC hmc hsc hpc hEuler hSum
  have hkc := isK3_of_euler24 hFundamentalEuler hClass SurfaceComplexData.curve MC
    hmc hpc hsc hf he
  have hproper : IsProper M.structureMap := by dsimp [RegularModel.structureMap]; infer_instance
  have hModule := CanonicalCotangentConstruction.differential_module ℚ hCotangent hExterior
    H.negative_curve.conormal_qc
  have hforms := CanonicalBundleDescent.canonical_descends ℚ ℂ hModule
    H.line_bundle_descent hDifferentials hFinite hPicard
  have hkq := descends_of_isPullback ℚ ℂ hCoh hforms M.scheme MC.scheme M.structureMap
    MC.structureMap (SurfaceRationalDescent.complexCoefficientMap H M) hpb
      hproper M.smooth M.geometricallyIntegral M.dimension hkc
  exact ⟨M,hm,hs,hp,hkq,(lemma_3_1_c hUnique M hm hs hp).2.2⟩

end
end Z2Z4Rank6.SurfaceInvolution
