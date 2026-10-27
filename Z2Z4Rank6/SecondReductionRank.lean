module

public import Z2Z4Rank6.SecondReductionRational
public import Z2Z4Rank6.ReductionCheckRank
public import Z2Z4Rank6.TorsionCongruence
public import Z2Z4Rank6.PointScaling

@[expose] public section

/-!
# Independence at the rational point in Section 8(d)

The hypotheses are Mazur's torsion theorem and the good-reduction homomorphism theorem.
-/

namespace Z2Z4Rank6.SecondReductionData

open SecondFamily Common.WeierstrassCoordinates

local instance : Fact (Nat.Prime 83) := ⟨by decide +kernel⟩

theorem ab_valuation_83 : padicValRat 83 ((a0:ℚ)*(b0:ℚ))=1 := by
  have hnat : padicValNat 83 5143156658866828800=1 := by
    rw [show (5143156658866828800:ℕ)=83*61965742877913600 by decide +kernel,
      padicValNat.mul (by decide +kernel) (by decide +kernel),
      padicValNat.self (by decide +kernel),
      padicValNat.eq_zero_of_not_dvd (by decide +kernel)]
  norm_num [a0,b0,padicValRat_def,padicValInt]
  exact hnat

theorem rational_torsion_exact (hMazur : MazurTorsionTheorem) :
    TorsionExact rationalCurve := by
  apply E_torsion_exact hMazur (a0:ℚ) (b0:ℚ)
  · norm_num [a0,b0]
  · exact not_isSquare_of_valuation_one ab_valuation_83
  · norm_num [a0,b0]

/-- The six signed rational points in the printed integral model are
independent. The finite-field matrix is linked by reduction homomorphisms. -/
theorem rationalPoint_linearIndependent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    LinearIndependent ℤ rationalPoint := by
  classical
  have hred : ∀ i : Fin 6, GoodReductionAt (primes i) rationalCurve := by
    intro i
    apply hReduction (primes i) rationalCurve inferInstance (integral_model i)
    rw [reduced_model i]
    infer_instance
  choose red hred using hred
  let mapped : ∀ i : Fin 6, RationalPoints rationalCurve →+ (curve i).toAffine.Point :=
    fun i => (pointEquivOfEq (reduced_model i)).toAddMonoidHom.comp (red i)
  have hpoints : ∀ i j : Fin 6, mapped i (rationalPoint j)=reducedPoint i j := by
    intro i j
    apply encode_injective (curve i)
    obtain ⟨hns,heq⟩ := hred i (rationalX j) (rationalY j)
      (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (rational_point_equation j))
      (rational_coordinates_integral i j).1 (rational_coordinates_integral i j).2
    change encode (pointEquivOfEq (reduced_model i) ((red i) (rationalPoint j)))=_
    rw [encode_pointEquivOfEq]
    change encode (red i (.some (rationalX j) (rationalY j) _))=_
    rw [heq]
    change some (residue (primes i) (rationalX j),residue (primes i) (rationalY j))=
      some ((reducedX i j : ZMod (primes i)),(reducedY i j : ZMod (primes i)))
    rw [(rational_coordinates_residue i j).1,(rational_coordinates_residue i j).2]
  let f : ∀ i : Fin 6, RationalPoints rationalCurve →+ (curve i).toAffine.Point :=
    fun i => (nsmulAddMonoidHom (multipliers i)).comp (mapped i)
  apply linearIndependent_of_three_torsion_rows rationalPoint f generator
    printedMatrix printedMatrix_isUnit generator_order
  · intro i Q hQ
    exact multiplied_hom_kills_torsion (rational_torsion_exact hMazur) (mapped i)
      _ (four_dvd_multiplier i) Q hQ
  · intro i j
    change multipliers i • mapped i (rationalPoint j)=_
    rw [hpoints]
    exact scalar_images i j

theorem baseCurve_eq_long : F baseW=PointScaling.curve (U baseW) ((V baseW)^2) := by
  ext <;> simp [F,twistedF,PointScaling.curve]

theorem scaled_curve :
    PointScaling.curve (scale^2*U baseW) (scale^4*(V baseW)^2)=rationalCurve := by
  ext <;> norm_num [PointScaling.curve,rationalCurve,E,U,V,baseW,baseS1,scale,lambda,a0,b0]

/-- The printed coordinate scaling as an additive equivalence. -/
def fiberScalingEquiv : (F baseW).toAffine.Point ≃+ rationalCurve.toAffine.Point :=
  ((PointScaling.pointCongr baseCurve_eq_long).trans
    (PointScaling.scaleEquiv (U baseW) ((V baseW)^2) scale (by norm_num [scale]))).trans
    (PointScaling.pointCongr scaled_curve)

/-- The same scaling is a Weierstrass variable change of the fiber. -/
theorem fiber_variableChange :
    scalingChange (Units.mk0 scale (by norm_num [scale])) • F baseW=
      rationalCurve := by
  have hF : F baseW=E ((baseS1-1)*(baseS1-lambda))
      ((baseS1+1)*(baseS1+lambda)) := F_split baseS1
  rw [hF,scalingChange_E]
  change E (scale*((baseS1-1)*(baseS1-lambda)))
    (scale*((baseS1+1)*(baseS1+lambda)))=rationalCurve
  rw [scale_parameters.1,scale_parameters.2]
  rfl

theorem fiber_torsion_exact (hMazur : MazurTorsionTheorem) :
    TorsionExact (F baseW) := by
  obtain ⟨e⟩ := rational_torsion_exact hMazur
  exact ⟨((fiberScalingEquiv.addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr fiberScalingEquiv.map_torsion)).trans e⟩

def fiberPoints : Fin 6 → (F baseW).toAffine.Point := by
  letI : (F basePoint.W).IsElliptic := baseFiberElliptic
  exact basePoint.sixPoints base_regular.1 base_regular.2.1 base_regular.2.2

theorem encode_fiberPoints (j : Fin 6) :
    encode (fiberPoints j)=some (basePoint.sixX j,basePoint.sixY j) := by
  fin_cases j <;> rfl

/-- The finite reduction certificate concerns the six specialized
sections, through the same printed scaling of x and y. -/
theorem fiberScaling_points (j : Fin 6) :
    fiberScalingEquiv (fiberPoints j)=rationalPoint j := by
  apply encode_injective rationalCurve
  change encode (PointScaling.pointCongr scaled_curve
    (PointScaling.scaleEquiv (U baseW) ((V baseW)^2) scale (by norm_num [scale])
      (PointScaling.pointCongr baseCurve_eq_long (fiberPoints j))))=_
  rw [PointScaling.encode_pointCongr,PointScaling.encode_scaleEquiv,
    PointScaling.encode_pointCongr,encode_fiberPoints]
  change some (scale^2*basePoint.sixX j,scale^3*basePoint.sixY j)=
    some (rationalX j,rationalY j)
  rw [← rationalX_eq_scaled_section,← rationalY_eq_scaled_section]

theorem fiberPoints_linearIndependent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    LinearIndependent ℤ fiberPoints := by
  apply LinearIndependent.of_comp fiberScalingEquiv.toIntLinearEquiv.toLinearMap
  have heq : fiberScalingEquiv.toIntLinearEquiv.toLinearMap ∘ fiberPoints=rationalPoint := by
    funext j
    exact fiberScaling_points j
  rw [heq]
  exact rationalPoint_linearIndependent hMazur hReduction

theorem rational_rank_at_least_six
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    RankAtLeastSix rationalCurve :=
  ⟨rationalPoint,rationalPoint_linearIndependent hMazur hReduction⟩

theorem fiber_rank_at_least_six
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    RankAtLeastSix (F baseW) :=
  ⟨fiberPoints,fiberPoints_linearIndependent hMazur hReduction⟩

end Z2Z4Rank6.SecondReductionData
