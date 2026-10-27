module

public import Z2Z4Rank6.ReductionCheckOriginal
public import Z2Z4Rank6.ReductionTheory
public import Z2Z4Rank6.CongruenceBase

@[expose] public section

/-!
# Independence from the printed reduction data

This is the group-theoretic assembly in Propositions 5.1 and 6.2 of
Manvir Jaswal, DOI 10.5281/zenodo.23437117. The reduction hypothesis is
`GoodReductionHomomorphisms`.
-/

namespace Z2Z4Rank6

open scoped BigOperators
open Common.WeierstrassCoordinates

/-- The group Z/2 × Z/4 is killed by 4. -/
theorem four_nsmul_torsion_model (x : ZMod 2 × ZMod 4) : (4 : ℕ) • x = 0 := by
  ext
  · change (4 : ℕ) • x.1 = 0
    rw [nsmul_eq_mul]
    have h : ((4 : ℕ) : ZMod 2) = 0 := by decide +kernel
    rw [h, zero_mul]
  · change (4 : ℕ) • x.2 = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- Exact torsion Z/2 × Z/4 implies that every torsion point is killed by 4. -/
theorem TorsionExact.four_nsmul_eq_zero {W : WeierstrassCurve ℚ}
    (hT : TorsionExact W) (Q : RationalPoints W) (hQ : IsOfFinAddOrder Q) :
    (4 : ℕ) • Q = 0 := by
  obtain ⟨e⟩ := hT
  let T : AddCommGroup.torsion (RationalPoints W) := ⟨Q, hQ⟩
  have h : (4 : ℕ) • T = 0 := by
    apply e.injective
    simpa only [map_nsmul, map_zero] using four_nsmul_torsion_model (e T)
  exact congrArg Subtype.val h

/-- Equality of Weierstrass equations identifies their point groups. -/
def pointEquivOfEq {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K}
    (h : W = W') : W.toAffine.Point ≃+ W'.toAffine.Point := by
  subst W'
  exact AddEquiv.refl _

/-- Transporting a point along equation equality preserves its coordinates. -/
theorem encode_pointEquivOfEq {K : Type*} [Field K] [DecidableEq K] {W W' : WeierstrassCurve K}
    (h : W = W') (P : W.toAffine.Point) :
    encode (pointEquivOfEq h P) = encode P := by
  subst W'
  rfl

/-- A multiplier divisible by 4 makes any homomorphism kill all torsion,
when the source torsion is Z/2 × Z/4. -/
theorem multiplied_hom_kills_torsion {W : WeierstrassCurve ℚ}
    {H : Type*} [AddCommGroup H] (hT : TorsionExact W)
    (f : RationalPoints W →+ H) (d : ℕ) (hd : 4 ∣ d)
    (Q : RationalPoints W) (hQ : IsOfFinAddOrder Q) : d • f Q = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [mul_nsmul, ← map_nsmul f 4 Q,
    hT.four_nsmul_eq_zero Q hQ, map_zero, nsmul_zero]

/-- Once the concrete model and coordinate congruences have been
proved, the published reduction theorem and the checked printed matrix
prove independence of the six specialized sections. -/
theorem sixPoints_linearIndependent_of_reduction_data
    (hReduction : GoodReductionHomomorphisms) (c : CPoint)
    [(X c.m).IsElliptic] (hm : c.m ≠ 0) (hT : TorsionExact (X c.m))
    (hIntegral : ∀ i : Fin 6, IntegralModelAt (ReductionData.primes i) (X c.m))
    (hModel : ∀ i : Fin 6,
      reducedModel (ReductionData.primes i) (X c.m) = ReductionData.originalCurve i)
    (hXi : ∀ i j : Fin 6, IntegralAt (ReductionData.primes i) (sixX c.m j))
    (hYi : ∀ i j : Fin 6, IntegralAt (ReductionData.primes i) (sixY c.m c.u c.v j))
    (hXr : ∀ i j : Fin 6, residue (ReductionData.primes i) (sixX c.m j) =
      sixX (ReductionData.localM i) j)
    (hYr : ∀ i j : Fin 6, residue (ReductionData.primes i) (sixY c.m c.u c.v j) =
      sixY (ReductionData.localM i) (ReductionData.localU i) (ReductionData.localV i) j) :
    LinearIndependent ℤ (sixPoints c.m c.u c.v c.u_sq c.v_sq hm c.u_ne_zero c.v_ne_zero) := by
  classical
  let P := sixPoints c.m c.u c.v c.u_sq c.v_sq hm c.u_ne_zero c.v_ne_zero
  have hred : ∀ i : Fin 6, GoodReductionAt (ReductionData.primes i) (X c.m) := by
    intro i
    apply hReduction (ReductionData.primes i) (X c.m) inferInstance (hIntegral i)
    rw [hModel i]
    infer_instance
  choose red hred using hred
  let mapped : ∀ i : Fin 6, RationalPoints (X c.m) →+
      (ReductionData.originalCurve i).toAffine.Point := fun i =>
    (pointEquivOfEq (hModel i)).toAddMonoidHom.comp (red i)
  have hpoints : ∀ i j : Fin 6, mapped i (P j) = ReductionData.originalPoint i j := by
    intro i j
    apply encode_injective (ReductionData.originalCurve i)
    obtain ⟨hns, heq⟩ := hred i (sixX c.m j) (sixY c.m c.u c.v j)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        (six_affine_equations c.m c.u c.v c.u_sq c.v_sq hm c.u_ne_zero c.v_ne_zero j)) (hXi i j) (hYi i j)
    change encode (pointEquivOfEq (hModel i) ((red i) (P j))) = _
    rw [encode_pointEquivOfEq]
    change encode (red i (.some (sixX c.m j) (sixY c.m c.u c.v j) _)) = _
    rw [heq]
    change some (residue (ReductionData.primes i) (sixX c.m j),
      residue (ReductionData.primes i) (sixY c.m c.u c.v j)) =
      some (sixX (ReductionData.localM i) j,
        sixY (ReductionData.localM i) (ReductionData.localU i) (ReductionData.localV i) j)
    rw [hXr, hYr]
  let f : ∀ i : Fin 6, RationalPoints (X c.m) →+
      (ReductionData.originalCurve i).toAffine.Point := fun i =>
    (nsmulAddMonoidHom (ReductionData.multipliers i)).comp (mapped i)
  apply linearIndependent_of_three_torsion_rows P f ReductionData.originalGenerator
    ReductionData.printedMatrix ReductionData.printedMatrix_isUnit
    ReductionData.originalGenerator_order
  · intro i Q hQ
    exact multiplied_hom_kills_torsion hT (mapped i) _
      (ReductionData.four_dvd_multiplier i) Q hQ
  · intro i j
    change ReductionData.multipliers i • mapped i (P j) = _
    rw [hpoints]
    exact ReductionData.original_scalar_images i j

/-- The six-prime coordinate congruences in Proposition 6.2. The separate
13-adic condition is used to obtain `TorsionExact`, not in this definition. -/
def SixPrimeCongruences (c : CPoint) : Prop :=
  ∀ i : Fin 6,
    IntegralAt (ReductionData.primes i) c.m ∧
    IntegralAt (ReductionData.primes i) c.u ∧
    IntegralAt (ReductionData.primes i) c.v ∧
    residue (ReductionData.primes i) c.m = residue (ReductionData.primes i) baseC0.m ∧
    residue (ReductionData.primes i) c.u = residue (ReductionData.primes i) baseC0.u ∧
    residue (ReductionData.primes i) c.v = residue (ReductionData.primes i) baseC0.v

/-- Every rational point satisfying the six-prime coordinate
congruences, with torsion Z/2 × Z/4, gives six integer-linearly independent
rational points on the original fiber. The hypothesis is the good-reduction theorem. -/
theorem rankAtLeastSix_of_congruences
    (hReduction : GoodReductionHomomorphisms) (c : CPoint)
    (hc : SixPrimeCongruences c) (hT : TorsionExact (X c.m)) :
    RankAtLeastSix (X c.m) := by
  have h0 := hc 0
  have : (X c.m).IsElliptic := X_good_of_congruent 0 h0.1 h0.2.2.2.1
  have hm : c.m ≠ 0 := by
    intro h
    have hD := denominator_unit_of_congruent 0 h0.1 h0.2.2.2.1
    simp [h, sectionDenominator] at hD
  refine ⟨sixPoints c.m c.u c.v c.u_sq c.v_sq hm c.u_ne_zero c.v_ne_zero, ?_⟩
  apply sixPoints_linearIndependent_of_reduction_data hReduction c hm hT
  · intro i
    exact X_integralModel (hc i).1
  · intro i
    exact reducedModel_X_of_congruent i (hc i).1 (hc i).2.2.2.1
  · intro i j
    have hi := hc i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).1
  · intro i j
    have hi := hc i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.1
  · intro i j
    have hi := hc i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.2.1
  · intro i j
    have hi := hc i
    exact (c.reduction_coordinates_of_congruent i hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2 j).2.2.2

end Z2Z4Rank6
