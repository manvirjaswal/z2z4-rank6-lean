import Z2Z4Rank6.ThirdTwistCoverProjective
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! The weighted Proj covers have proper rational structure maps.
The degree-zero ring is proved to be Q using the strictly positive weights.
Evaluation at the cone origin (0,0,0,0,0) proves the coordinate quotients nontrivial.
-/

namespace Z2Z4Rank6.ThirdTwistCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

theorem weights_pos (i : Fin 5) : 0<weights i := by fin_cases i <;> decide
theorem weights_ne_zero (i : Fin 5) : weights i≠0 := Nat.ne_of_gt (weights_pos i)

def evaluation  : CoordinateRing→ₐ[ℚ]ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal) (MvPolynomial.aeval ![(0:ℚ),0,0,0,0]) (by
    have hker : definingIdeal≤RingHom.ker
        (MvPolynomial.aeval ![(0:ℚ),0,0,0,0]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (MvPolynomial.aeval ![(0:ℚ),0,0,0,0]) (relation i)=0
      fin_cases i <;> norm_num [relation,rootIndex,ThirdTwistCoverEquations.binary]
    intro p hp
    exact hker hp)

instance coordinateRing_nontrivial  : Nontrivial (CoordinateRing) :=
  (evaluation).toRingHom.domain_nontrivial

instance gradeZero_nontrivial  : Nontrivial (grading 0) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h : (0:CoordinateRing)=1)

theorem degreeZero_eq_rat  (r : grading 0) :
    ∃q : ℚ,r=algebraMap ℚ (grading 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.IsWeightedHomogeneous weights 0 := hp
  have hpC : p=MvPolynomial.C (p.coeff 0) :=
    hp0.weightedHomogeneousComponent_same.symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero p weights_ne_zero)
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing)=algebraMap ℚ (CoordinateRing) (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

instance gradeZero_scalarTower  : IsScalarTower ℚ (grading 0) (CoordinateRing) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=grading 0) (A:=CoordinateRing) rfl

def degreeZeroEquiv  : ℚ≃+*grading 0 :=
  RingEquiv.ofBijective (algebraMap ℚ (grading 0))
    ⟨(algebraMap ℚ (grading 0)).injective,fun r => by
      obtain ⟨q,hq⟩ := degreeZero_eq_rat r
      exact ⟨q,hq.symm⟩⟩

def structureMap  : scheme⟶Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero (grading) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))

instance coordinateRing_finiteType  :
    Algebra.FiniteType (grading 0) (CoordinateRing) := by
  let : Algebra.FiniteType ℚ (CoordinateRing) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ (grading 0) (CoordinateRing)

instance structureMap_proper  : IsProper (structureMap) := by
  have hIso : IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading 0)))) := by
    change IsIso (Scheme.Spec.mapIso (degreeZeroEquiv).toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

abbrev ChartRing  (k : Fin 5) := HomogeneousLocalization.Away (grading) (coordinate k)
instance chartAlgebra  (k : Fin 5) : Algebra ℚ (ChartRing k) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading) (Submonoid.powers (coordinate k))).comp
    (algebraMap ℚ (grading 0))).toAlgebra

def chartInclusion  (k : Fin 5) : Spec (CommRingCat.of (ChartRing k))⟶scheme :=
  Proj.awayι (grading) (coordinate k) (coordinate_degree k) (weights_pos k)

theorem chartInclusion_structureMap  (k : Fin 5) :
    chartInclusion k≫structureMap=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartRing k))) := by
  dsimp only [chartInclusion,structureMap,scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero,←Spec.map_comp]
  rfl

end
end Z2Z4Rank6.ThirdTwistCoverProjective
