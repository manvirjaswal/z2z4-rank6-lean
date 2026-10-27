import Z2Z4Rank6.GReductionRational
import Z2Z4Rank6.ReductionCheckRank
import Z2Z4Rank6.TorsionCongruence
import Z2Z4Rank6.PointScaling

/-!
# Independence at the rational point in Proposition 7.2(b)

The hypotheses are Mazur's torsion theorem and the good-reduction homomorphism theorem.
-/

namespace Z2Z4Rank6.GReductionData

open GFunctionField Common.WeierstrassCoordinates

local instance prime43Fact : Fact (Nat.Prime 43) := ⟨by decide +kernel⟩

theorem ab_valuation_43 : padicValRat 43 ((a0:ℚ)*(b0:ℚ))=1 := by
  have hnat : padicValNat 43 80624499725060096=1 := by
    rw [show (80624499725060096:ℕ)=43*1874988365699072 by decide +kernel,
      padicValNat.mul (by decide +kernel) (by decide +kernel),
      padicValNat.self (by decide +kernel),
      padicValNat.eq_zero_of_not_dvd (by decide +kernel)]
  norm_num [a0,b0,padicValRat_def,padicValInt]
  exact hnat

theorem rational_torsion_exact (hMazur : MazurTorsionTheorem) :
    TorsionExact rationalCurve := by
  apply E_torsion_exact hMazur (a0:ℚ) (b0:ℚ)
  · norm_num [a0,b0]
  · exact not_isSquare_of_valuation_one ab_valuation_43
  · norm_num [a0,b0]

/-- The five signed rational points in the printed integral model are
independent. The finite-field matrix is linked by reduction homomorphisms. -/
theorem rationalPoint_linearIndependent
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    LinearIndependent ℤ rationalPoint := by
  classical
  have hred : ∀ i : Fin 5, GoodReductionAt (primes i) rationalCurve := by
    intro i
    apply hReduction (primes i) rationalCurve inferInstance (integral_model i)
    rw [reduced_model i]
    infer_instance
  choose red hred using hred
  let mapped : ∀ i : Fin 5, RationalPoints rationalCurve →+ (curve i).toAffine.Point :=
    fun i => (pointEquivOfEq (reduced_model i)).toAddMonoidHom.comp (red i)
  have hpoints : ∀ i j : Fin 5, mapped i (rationalPoint j)=reducedPoint i j := by
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
  let f : ∀ i : Fin 5, RationalPoints rationalCurve →+ (curve i).toAffine.Point :=
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

def longA : ℚ := (a baseM)^2+(b baseM)^2
def longB : ℚ := (a baseM)^2*(b baseM)^2

theorem baseCurve_eq_long : X baseM=PointScaling.curve longA longB := by
  ext <;> simp [X,E,longA,longB,PointScaling.curve]

theorem scaled_curve :
    PointScaling.curve (scale^2*longA) (scale^4*longB)=rationalCurve := by
  ext <;> norm_num [PointScaling.curve,rationalCurve,E,longA,longB,a,b,baseM,scale,a0,b0]

def fiberScalingEquiv : (X baseM).toAffine.Point ≃+ rationalCurve.toAffine.Point :=
  ((PointScaling.pointCongr baseCurve_eq_long).trans
    (PointScaling.scaleEquiv longA longB scale (by norm_num [scale]))).trans
    (PointScaling.pointCongr scaled_curve)

theorem fiber_variableChange :
    scalingChange (Units.mk0 scale (by norm_num [scale])) • X baseM=rationalCurve := by
  rw [X,scalingChange_E]
  change E (scale*a baseM) (scale*b baseM)=rationalCurve
  rw [scale_parameters.1,scale_parameters.2]
  rfl

theorem fiber_torsion_exact (hMazur : MazurTorsionTheorem) :
    TorsionExact (X baseM) := by
  obtain ⟨e⟩ := rational_torsion_exact hMazur
  exact ⟨((fiberScalingEquiv.addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr fiberScalingEquiv.map_torsion)).trans e⟩

def fiberPoints : Fin 5 → (X baseM).toAffine.Point :=
  fivePoints baseM baseEta base_on_curve base_regular.1 base_regular.2

theorem encode_fiberPoints (j : Fin 5) :
    encode (fiberPoints j)=some (fiveX baseM baseEta j,fiveY baseM baseEta j) :=
  encode_fivePoints baseM baseEta base_on_curve base_regular.1 base_regular.2 j

theorem fiberScaling_points (j : Fin 5) :
    fiberScalingEquiv (fiberPoints j)=rationalPoint j := by
  apply encode_injective rationalCurve
  change encode (PointScaling.pointCongr scaled_curve
    (PointScaling.scaleEquiv longA longB scale (by norm_num [scale])
      (PointScaling.pointCongr baseCurve_eq_long (fiberPoints j))))=_
  rw [PointScaling.encode_pointCongr,PointScaling.encode_scaleEquiv,
    PointScaling.encode_pointCongr,encode_fiberPoints]
  change some (scale^2*fiveX baseM baseEta j,scale^3*fiveY baseM baseEta j)=
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

theorem rational_rank_at_least_five
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    ∃ P : Fin 5 → RationalPoints rationalCurve, LinearIndependent ℤ P :=
  ⟨rationalPoint,rationalPoint_linearIndependent hMazur hReduction⟩

theorem fiber_rank_at_least_five
    (hMazur : MazurTorsionTheorem) (hReduction : GoodReductionHomomorphisms) :
    ∃ P : Fin 5 → RationalPoints (X baseM), LinearIndependent ℤ P :=
  ⟨fiberPoints,fiberPoints_linearIndependent hMazur hReduction⟩

end Z2Z4Rank6.GReductionData
