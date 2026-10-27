import Z2Z4Rank6.TorsionCoverProjective
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! The weighted Proj covers have proper rational structure maps.
The degree-zero ring is proved to be Q using the strictly positive weights.
Evaluation at (1,35,35,1,0) proves the coordinate quotients nontrivial.
-/

namespace Z2Z4Rank6.TorsionCoverProjective
noncomputable section
open scoped Classical
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

theorem weights_pos (i : Fin 5) : 0<weights i := by fin_cases i <;> decide
theorem weights_ne_zero (i : Fin 5) : weights i≠0 := Nat.ne_of_gt (weights_pos i)

def evaluation (ε : Bool) : CoordinateRing ε→ₐ[ℚ]ℚ :=
  Ideal.Quotient.liftₐ (definingIdeal ε) (MvPolynomial.aeval ![(1:ℚ),35,35,1,0]) (by
    have hker : definingIdeal ε≤RingHom.ker
        (MvPolynomial.aeval ![(1:ℚ),35,35,1,0]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change (MvPolynomial.aeval ![(1:ℚ),35,35,1,0]) (relation ε i)=0
      fin_cases i <;> norm_num [relation,HeightInvariantForms.binaryA,HeightInvariantForms.binaryB]
    intro p hp
    exact hker hp)

instance coordinateRing_nontrivial (ε : Bool) : Nontrivial (CoordinateRing ε) :=
  (evaluation ε).toRingHom.domain_nontrivial

instance gradeZero_nontrivial (ε : Bool) : Nontrivial (grading ε 0) := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  exact zero_ne_one (congrArg Subtype.val h : (0:CoordinateRing ε)=1)

theorem degreeZero_eq_rat (ε : Bool) (r : grading ε 0) :
    ∃q : ℚ,r=algebraMap ℚ (grading ε 0) q := by
  obtain ⟨p,hp,he⟩ := r.property
  have hp0 : p.IsWeightedHomogeneous weights 0 := hp
  have hpC : p=MvPolynomial.C (p.coeff 0) :=
    hp0.weightedHomogeneousComponent_same.symm.trans
      (MvPolynomial.weightedHomogeneousComponent_zero p weights_ne_zero)
  refine ⟨p.coeff 0,Subtype.ext ?_⟩
  change (r:CoordinateRing ε)=algebraMap ℚ (CoordinateRing ε) (p.coeff 0)
  rw [←he,hpC]
  simp only [MvPolynomial.coeff_C]
  rfl

instance gradeZero_scalarTower (ε : Bool) : IsScalarTower ℚ (grading ε 0) (CoordinateRing ε) :=
  IsScalarTower.of_algebraMap_eq' (R:=ℚ) (S:=grading ε 0) (A:=CoordinateRing ε) rfl

def degreeZeroEquiv (ε : Bool) : ℚ≃+*grading ε 0 :=
  RingEquiv.ofBijective (algebraMap ℚ (grading ε 0))
    ⟨(algebraMap ℚ (grading ε 0)).injective,fun r => by
      obtain ⟨q,hq⟩ := degreeZero_eq_rat ε r
      exact ⟨q,hq.symm⟩⟩

def structureMap (ε : Bool) : scheme ε⟶Spec (CommRingCat.of ℚ) :=
  Proj.toSpecZero (grading ε) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading ε 0)))

instance coordinateRing_finiteType (ε : Bool) :
    Algebra.FiniteType (grading ε 0) (CoordinateRing ε) := by
  let : Algebra.FiniteType ℚ (CoordinateRing ε) := inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ (grading ε 0) (CoordinateRing ε)

instance structureMap_proper (ε : Bool) : IsProper (structureMap ε) := by
  have hIso : IsIso (Spec.map (CommRingCat.ofHom (algebraMap ℚ (grading ε 0)))) := by
    change IsIso (Scheme.Spec.mapIso (degreeZeroEquiv ε).toCommRingCatIso.op).hom
    infer_instance
  dsimp only [structureMap]
  infer_instance

abbrev ChartRing (ε : Bool) (k : Fin 5) := HomogeneousLocalization.Away (grading ε) (coordinate ε k)
instance chartAlgebra (ε : Bool) (k : Fin 5) : Algebra ℚ (ChartRing ε k) :=
  ((HomogeneousLocalization.fromZeroRingHom (grading ε) (Submonoid.powers (coordinate ε k))).comp
    (algebraMap ℚ (grading ε 0))).toAlgebra

def chartInclusion (ε : Bool) (k : Fin 5) : Spec (CommRingCat.of (ChartRing ε k))⟶scheme ε :=
  Proj.awayι (grading ε) (coordinate ε k) (coordinate_degree ε k) (weights_pos k)

theorem chartInclusion_structureMap (ε : Bool) (k : Fin 5) :
    chartInclusion ε k≫structureMap ε=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (ChartRing ε k))) := by
  dsimp only [chartInclusion,structureMap,scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero,←Spec.map_comp]
  rfl

end
end Z2Z4Rank6.TorsionCoverProjective
