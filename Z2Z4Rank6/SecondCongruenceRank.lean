module

public import Z2Z4Rank6.SecondCongruenceReduction
public import Z2Z4Rank6.SecondCongruenceCoordinates
public import Z2Z4Rank6.SecondTorsionNeighborhood

@[expose] public section

/-! Six independent points on every second-family fiber in the checked
six-prime residue class, once its torsion is Z/2 × Z/4. -/
namespace Z2Z4Rank6
open SecondFamily Common.WeierstrassCoordinates

private theorem second_scaled_point_nonsingular (P:G2Point ℚ)
    (hW:P.W≠0) (hA:qA P.W≠0) (hB:qB P.W≠0) [(F P.W).IsElliptic] (j:Fin 6) :
    (secondScaledCurve P.W).toAffine.Nonsingular
      (SecondReductionData.scale^2*P.sixX j) (SecondReductionData.scale^3*P.sixY j) := by
  apply PointScaling.scale_nonsingular _ _ _ (by norm_num [SecondReductionData.scale])
  have hn:=WeierstrassCurve.Affine.equation_iff_nonsingular.mp (P.six_affine_equations hW hA hB j)
  rw [secondF_eq_long] at hn
  exact hn

private theorem second_scaled_sixPoints_eq (P:G2Point ℚ)
    (hW:P.W≠0) (hA:qA P.W≠0) (hB:qB P.W≠0) [(F P.W).IsElliptic] (j:Fin 6) :
    secondFiberScaling P.W (P.sixPoints hW hA hB j)=
      .some (SecondReductionData.scale^2*P.sixX j) (SecondReductionData.scale^3*P.sixY j)
        (second_scaled_point_nonsingular P hW hA hB j) := by
  apply encode_injective (secondScaledCurve P.W)
  change encode (PointScaling.scaleEquiv (U P.W) ((V P.W)^2) SecondReductionData.scale
    (by norm_num [SecondReductionData.scale])
    (PointScaling.pointCongr (secondF_eq_long P.W) (P.sixPoints hW hA hB j)))=_
  rw [PointScaling.encode_scaleEquiv,PointScaling.encode_pointCongr,P.encode_sixPoints]
  rfl

/-- The exact signed section tuple itself is independent, by the checked
matrix and good-reduction homomorphisms on the nearby scaled model. -/
theorem second_sixPoints_linearIndependent_of_congruences
    (hReduction:GoodReductionHomomorphisms) (P:G2Point ℚ)
    (hCong:∀i:Fin 6,SecondCongruentAt i P) (hTor:TorsionExact (F P.W))
    [(F P.W).IsElliptic] (hW:P.W≠0) (hA:qA P.W≠0) (hB:qB P.W≠0) :
    LinearIndependent ℤ (P.sixPoints hW hA hB) := by
  classical
  let Q : Fin 6→RationalPoints (secondScaledCurve P.W) :=
    fun j=>secondFiberScaling P.W (P.sixPoints hW hA hB j)
  have hScaledTor:TorsionExact (secondScaledCurve P.W) := by
    obtain ⟨e⟩:=hTor
    exact ⟨(((secondFiberScaling P.W).symm.addSubgroupMap _).trans
      (AddEquiv.addSubgroupCongr (secondFiberScaling P.W).symm.map_torsion)).trans e⟩
  have hScaledElliptic:(secondScaledCurve P.W).IsElliptic:=secondScaledCurve_elliptic P.W
  have hred:∀i:Fin 6,GoodReductionAt (SecondReductionData.primes i) (secondScaledCurve P.W) := by
    intro i
    apply hReduction _ _ hScaledElliptic (second_scaled_integralModel i P (hCong i))
    rw [second_scaled_reducedModel i P (hCong i)]
    infer_instance
  choose red hred using hred
  let mapped : ∀i:Fin 6,RationalPoints (secondScaledCurve P.W)→+(SecondReductionData.curve i).toAffine.Point :=
    fun i=>(pointEquivOfEq (second_scaled_reducedModel i P (hCong i))).toAddMonoidHom.comp (red i)
  have hpoints:∀i j:Fin 6,mapped i (Q j)=SecondReductionData.reducedPoint i j := by
    intro i j
    apply encode_injective (SecondReductionData.curve i)
    have hc:=second_scaled_coordinates i j P (hCong i)
    obtain ⟨hns,heq⟩:=hred i (SecondReductionData.scale^2*P.sixX j)
      (SecondReductionData.scale^3*P.sixY j) (second_scaled_point_nonsingular P hW hA hB j) hc.1 hc.2.1
    change encode (pointEquivOfEq _ ((red i) (Q j)))=_
    rw [encode_pointEquivOfEq]
    change encode ((red i) (secondFiberScaling P.W (P.sixPoints hW hA hB j)))=_
    rw [second_scaled_sixPoints_eq,heq]
    change some (residue _ (SecondReductionData.scale^2*P.sixX j),
      residue _ (SecondReductionData.scale^3*P.sixY j))=
      some ((SecondReductionData.reducedX i j:ZMod (SecondReductionData.primes i)),
        (SecondReductionData.reducedY i j:ZMod (SecondReductionData.primes i)))
    rw [hc.2.2.1,hc.2.2.2]
  let f:∀i:Fin 6,RationalPoints (secondScaledCurve P.W)→+(SecondReductionData.curve i).toAffine.Point :=
    fun i=>(nsmulAddMonoidHom (SecondReductionData.multipliers i)).comp (mapped i)
  have hLI:LinearIndependent ℤ Q := by
    apply linearIndependent_of_three_torsion_rows Q f SecondReductionData.generator
      SecondReductionData.printedMatrix SecondReductionData.printedMatrix_isUnit SecondReductionData.generator_order
    · intro i R hR
      exact multiplied_hom_kills_torsion hScaledTor (mapped i) _ (SecondReductionData.four_dvd_multiplier i) R hR
    · intro i j
      change SecondReductionData.multipliers i • mapped i (Q j)=_
      rw [hpoints]
      exact SecondReductionData.scalar_images i j
  exact LinearIndependent.of_comp (secondFiberScaling P.W).toIntLinearEquiv.toLinearMap hLI

/-- A rank-six fiber at every point of the six-prime congruence set,
provided exact torsion is supplied by the separately proved 3-adic class. -/
theorem second_rankAtLeastSix_of_congruences
    (hReduction:GoodReductionHomomorphisms) (P:G2Point ℚ)
    (hCong:P∈SecondCongruenceSet) (hTor:TorsionExact (F P.W)) : RankAtLeastSix (F P.W) := by
  let : (F P.W).IsElliptic:=second_elliptic_of_congruent 0 P (hCong 0)
  obtain ⟨hW,hA,hB⟩:=second_regular_of_congruent 0 P (hCong 0)
  exact ⟨P.sixPoints hW hA hB,
    second_sixPoints_linearIndependent_of_congruences hReduction P hCong hTor hW hA hB⟩

/-- The printed 3-adic torsion test and the six-prime matrix prove the full fiber conclusion. -/
theorem second_fiber_of_theta_congruences
    (hMazur:MazurTorsionTheorem) (hReduction:GoodReductionHomomorphisms)
    (P:G2Point ℚ) (hCong:P∈SecondCongruenceSet) (theta:ℚ)
    (hTheta:ThetaNear3 theta) (hW:P.W=(thetaS1 theta)^2) :
    (F P.W).IsElliptic ∧ TorsionExact (F P.W) ∧ RankAtLeastSix (F P.W) := by
  have hT:TorsionExact (F P.W):=by rw [hW]; exact F_theta_torsion_exact hMazur theta hTheta
  exact ⟨second_elliptic_of_congruent 0 P (hCong 0),hT,
    second_rankAtLeastSix_of_congruences hReduction P hCong hT⟩

end Z2Z4Rank6
