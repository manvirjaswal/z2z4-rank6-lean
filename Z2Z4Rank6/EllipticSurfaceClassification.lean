module

public import Z2Z4Rank6.EllipticSurfaceStatements
public import Common.Elliptic.SurfaceFundamentalLineBundle
public import Common.AlgebraicGeometry.CanonicalBundleDescent
public import Common.Elliptic.EllipticSurfaceSections
public import Common.Elliptic.SurfaceEulerCharacteristic
public import Common.AlgebraicGeometry.CanonicalCotangentConstruction

@[expose] public section

/-!
# The projective elliptic K3 surface

The rational minimal projective model and its section are supplied by
the two separate assertions of Leterrier, Remark 1.3.9, p. 36.
Constant-field pullbacks give its complex extension. The singular-fiber
Euler sum and Miranda's degree formula give fundamental-line degree 2;
Miranda's K3 clause and canonical/cohomology descent finish the result.
-/
namespace Z2Z4Rank6.EllipticSurfaceClassification
noncomputable section
open AlgebraicGeometry CategoryTheory
open Common.AlgebraicGeometry Common.AlgebraicGeometry.K3BaseChange
open Common.Elliptic.SurfaceModel Common.Elliptic.SurfaceDescentSources
open Common.Elliptic.ComplexEllipticSurfaceTheorems
open Common.Elliptic.SurfaceFundamentalLineBundle
open Common.Elliptic.EllipticSurfaceSections
open SurfaceBadParameters
set_option backward.isDefEq.respectTransparency false

theorem euler_eq_24 (hLocal : MirandaTableIV31) (M : SurfaceComplexGeometry.Model)
    (hm : M.IsRelativelyMinimal) (hs : M.HasSection)
    (hp : ProjectiveScheme.IsProjective ℂ M.scheme M.structureMap)
    (hEuler : SchuttShiodaSection67FiberEuler)
    (hSum : Common.Elliptic.SurfaceEulerCharacteristic.SchuttShiodaTheorem610) :
    ComplexPointsTopology.HasFiniteHomology ℂ M.scheme M.structureMap 4 ∧
    ComplexPointsTopology.euler ℂ M.scheme M.structureMap 4=24 := by
  have hMult : Common.Elliptic.SurfaceEulerCharacteristic.HasMultiplicativeFiber M :=
    ⟨parameter 0,order 0,by norm_num [order],SurfaceComplexGeometry.fiber_types hLocal M hm hs 0⟩
  obtain ⟨hf,he⟩ := hSum SurfaceComplexData.curve M hm hs hp hMult support
    (SurfaceComplexGeometry.good_elsewhere hLocal M hm hs)
  refine ⟨hf,he.trans ?_⟩
  calc
    _=∑ i : Fin 9,ComplexPointsTopology.euler ℂ
        (fiberOver M (parameter i)).left (fiberOver M (parameter i)).hom 2 := by
      rw [support,Finset.sum_image]
      intro a _ b _ h
      exact parameter_injective h
    _=∑ i : Fin 9,(order i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (SurfaceComplexGeometry.local_euler_numbers hLocal M hm hs hEuler i).2
    _=24 := by norm_num [order,Fin.sum_univ_succ]

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
    EllipticSurfaceStatements.DiscriminantStatement ∧ EllipticSurfaceStatements.GeometryStatement := by
  refine ⟨EllipticSurfaceStatements.discriminant_statement,?_⟩
  obtain ⟨M,hm,hs,hp⟩ :=
    model_with_section ℚ hModels hSections SurfaceRationalData.curve inferInstance
  let MC := SurfaceRationalDescent.complexModel H M
  have hmc := SurfaceRationalDescent.complexModel_isRelativelyMinimal H M hm hs hp
  have hsc := SurfaceRationalDescent.complexModel_hasSection H M hs
  have hpb := SurfaceRationalDescent.complexModel_isPullback H M
  have hpc := H.projective_baseChange ℚ ℂ M.scheme MC.scheme M.structureMap MC.structureMap
    (SurfaceRationalDescent.complexCoefficientMap H M) hpb hp
  obtain ⟨hf,he⟩ := euler_eq_24 hLocal MC hmc hsc hpc hEuler hSum
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
  have hlocal := SurfaceComplexGeometry.local_euler_numbers hLocal MC hmc hsc hEuler
  have hsum : (∑ i : Fin 9,ComplexPointsTopology.euler ℂ
      (fiberOver MC (parameter i)).left (fiberOver MC (parameter i)).hom 2)=24 := by
    calc
      _=∑ i : Fin 9,(order i : ℤ) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hlocal i).2
      _=24 := by norm_num [order,Fin.sum_univ_succ]
  exact ⟨M,hm,hs,hkq,MC,hmc,hsc,hkc,
    ⟨SurfaceRationalDescent.complexCoefficientMap H M,hpb⟩,hf,he,
    fun i=>⟨SurfaceComplexGeometry.fiber_types hLocal MC hmc hsc i,hlocal i⟩,
    hsum,SurfaceComplexGeometry.all_geometric_fibers hLocal MC hmc hsc⟩

end
end Z2Z4Rank6.EllipticSurfaceClassification
