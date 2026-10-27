module

public import Z2Z4Rank6.SecondLocalMaps
public import Z2Z4Rank6.SecondTorsionNeighborhood
public import Z2Z4Rank6.LocalTopology
public import Z2Z4Rank6.CompactRecurrence

@[expose] public section

/-!
# Infinitely many G2 points in the printed 3-adic neighborhood

Compact recurrence is applied to the J2(Q3) point group, at a checked
rational center. The explicit rational quartic and conic maps transport an
infinite subset into the theta-neighborhood of Remark 8.2. The hypotheses are the
torsion-integrality and local-topology theorems.
-/
namespace Z2Z4Rank6
noncomputable section
open Set Filter Topology
open scoped Topology

local instance secondLocalInfinitudePrimeThree:Fact (Nat.Prime 3) := ⟨by decide⟩
local instance secondLocalInfinitudePadicDecidableEq:DecidableEq ℚ_[3] := Classical.decEq _

abbrev J2Local:WeierstrassCurve ℚ_[3] := J2.baseChange ℚ_[3]
instance secondLocal_isElliptic:J2Local.IsElliptic :=
  inferInstanceAs (J2.map (algebraMap ℚ ℚ_[3])).IsElliptic

def secondPointToLocal:RationalPoints J2→+J2Local.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W':=J2)
    (Algebra.ofId ℚ ℚ_[3]:ℚ→ₐ[ℚ]ℚ_[3])

theorem secondPointToLocal_injective:Function.Injective secondPointToLocal :=
  WeierstrassCurve.Affine.Point.map_injective (W':=J2)
    (Algebra.ofId ℚ ℚ_[3]:ℚ→ₐ[ℚ]ℚ_[3])

theorem secondLocal_equation_iff(x y:ℚ_[3]):
    J2Local.toAffine.Equation x y ↔ y^2=(x+102809641014)*(x-51068871386)*(x-51740769627) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [J2Local,J2,WeierstrassCurve.baseChange,WeierstrassCurve.map]
  ring_nf

def secondLocalC0:AffineEquationPoints J2Local :=
  ⟨secondJacobianCoordinatesC0,(secondLocal_equation_iff _ _).mpr secondCoordinatesC0_equation⟩

theorem secondLocalC0_embedding:
    affinePointEmbedding J2Local secondLocalC0=secondPointToLocal secondJacobianC0 := by
  simp only [affinePointEmbedding,secondLocalC0,secondPointToLocal,secondJacobianC0,
    WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.map]
  congr 1 <;> norm_num [secondJacobianCoordinatesC0]

def secondThetaBall(r:ℝ):Set ℚ_[3] := {t | ‖t-(857/140:ℚ_[3])‖<r}

theorem secondThetaBall_mem_nhds(r:ℝ)(hr:0<r):
    secondThetaBall r∈𝓝 (857/140:ℚ_[3]) := by
  apply (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds
  change ‖(857/140:ℚ_[3])-(857/140:ℚ_[3])‖<r
  simpa only [sub_self,norm_zero] using hr

def secondCurveNeighborhood(r:ℝ):Set J2Local.toAffine.Point :=
  affinePointEmbedding J2Local '' {xy:AffineEquationPoints J2Local |
    secondQuarticTheta xy.val.1 xy.val.2∈secondThetaBall r}

theorem secondCurveNeighborhood_mem_nhds [TopologicalSpace J2Local.toAffine.Point]
    (hchart:IsOpenEmbedding (affinePointEmbedding J2Local))(r:ℝ)(hr:0<r):
    secondCurveNeighborhood r∈𝓝 (secondPointToLocal secondJacobianC0) := by
  have hc:{z:ℚ_[3]×ℚ_[3] | secondQuarticTheta z.1 z.2∈secondThetaBall r}∈
      𝓝 secondJacobianCoordinatesC0 := by
    apply (secondQuarticTheta_continuousAt _ secondCoordinatesC0_denom_ne_zero).preimage_mem_nhds
    rw [secondCoordinatesC0_theta]
    exact secondThetaBall_mem_nhds r hr
  have he:=affine_neighborhood J2Local hchart secondLocalC0 hc
  rw [secondLocalC0_embedding] at he
  exact he

theorem secondCurveNeighborhood_some_bound(r:ℝ)(x y:ℚ)(h:J2.toAffine.Nonsingular x y)
    (hP:secondPointToLocal (.some x y h)∈secondCurveNeighborhood r):
    ‖((secondQuarticTheta x y:ℚ):ℚ_[3])-(857/140:ℚ_[3])‖<r := by
  obtain ⟨xy,hxy,he⟩ := hP
  have hc:xy.val=((x:ℚ_[3]),(y:ℚ_[3])) := by
    change WeierstrassCurve.Affine.Point.some xy.val.1 xy.val.2 _=
      WeierstrassCurve.Affine.Point.some (x:ℚ_[3]) (y:ℚ_[3]) _ at he
    exact Prod.ext (WeierstrassCurve.Affine.Point.some.inj he).1
      (WeierstrassCurve.Affine.Point.some.inj he).2
  change ‖secondQuarticTheta xy.val.1 xy.val.2-(857/140:ℚ_[3])‖<r at hxy
  rw [hc] at hxy
  have hm:=map_secondQuarticTheta (Rat.castHom ℚ_[3]) x y
  change ((secondQuarticTheta x y:ℚ):ℚ_[3])=secondQuarticTheta (x:ℚ_[3]) (y:ℚ_[3]) at hm
  rw [←hm] at hxy
  exact hxy

theorem secondThetaNear3_of_padic_bound(t:ℚ)
    (h:‖(t:ℚ_[3])-(857/140:ℚ_[3])‖<(3:ℝ)^(-5:ℤ)):
    SecondFamily.ThetaNear3 t := by
  by_cases heq:t=SecondFamily.baseTheta
  · exact Or.inl heq
  · apply Or.inr
    have hcast:((t-SecondFamily.baseTheta:ℚ):ℚ_[3])≠0 := by exact_mod_cast (sub_ne_zero.mpr heq)
    have hn:‖((t-SecondFamily.baseTheta:ℚ):ℚ_[3])‖<(3:ℝ)^(-5:ℤ) := by
      change ‖((t-(857/140):ℚ):ℚ_[3])‖<(3:ℝ)^(-5:ℤ)
      simpa only [Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using h
    have hle:‖((t-SecondFamily.baseTheta:ℚ):ℚ_[3])‖≤(3:ℝ)^(-6:ℤ) :=
      (Padic.norm_lt_pow_iff_norm_le_pow_sub_one _ (-5)).1 hn
    rw [Padic.norm_eq_zpow_neg_valuation hcast,Padic.valuation_ratCast] at hle
    have hle':(3:ℝ)^(-padicValRat 3 (t-SecondFamily.baseTheta))≤(3:ℝ)^(-6:ℤ) := by
      simpa only [Nat.cast_ofNat] using hle
    have hv:= (zpow_le_zpow_iff_right₀ (by norm_num:1<(3:ℝ))).mp hle' 
    omega

/-- The parameter neighborhood on the three-equation base. -/
def secondThetaNeighborhoodSet:Set (SecondFamily.G2Point ℚ) :=
  {P | ∃t:ℚ,SecondFamily.ThetaNear3 t ∧ P.W=(SecondFamily.thetaS1 t)^2 ∧
    P.s1=SecondFamily.thetaS1 t ∧ P.s2=SecondFamily.thetaS2 t}

def secondLocalToG2(P:RationalPoints J2):SecondFamily.G2Point ℚ := by
  classical
  exact if h:secondJacobianQuarticChart P then
    secondQuarticToG2 (secondJacobianToQuartic ⟨P,h⟩)
  else secondQuarticToG2 secondQuarticC0

theorem secondLocalToG2_injOn:
    Set.InjOn secondLocalToG2 {P:RationalPoints J2 | secondJacobianQuarticChart P} := by
  intro P hP Q hQ he
  change secondJacobianQuarticChart P at hP
  change secondJacobianQuarticChart Q at hQ
  simp only [secondLocalToG2,dite_eq_left hP,dite_eq_left hQ] at he
  have hi:=secondJacobianToQuartic_injective (secondQuarticToG2_injective he)
  exact congrArg Subtype.val hi

theorem secondLocalToG2_mem_neighborhood(x y:ℚ)(h:J2.toAffine.Nonsingular x y)
    (hchart:secondJacobianQuarticChart (.some x y h))
    (ht:SecondFamily.ThetaNear3 (secondQuarticTheta x y)):
    secondLocalToG2 (.some x y h)∈secondThetaNeighborhoodSet := by
  rw [secondLocalToG2,dite_eq_left hchart]
  exact ⟨secondQuarticTheta x y,ht,rfl,rfl,rfl⟩

theorem infinite_secondThetaNeighborhoodSet
    (hSilvermanVII34:OddPrimeTorsionIntegrality)(hLocal:LocalEllipticTopology):
    secondThetaNeighborhoodSet.Infinite := by
  obtain ⟨T,hT⟩ := hLocal 3 J2Local inferInstance
  let : TopologicalSpace J2Local.toAffine.Point := T
  let : CompactSpace J2Local.toAffine.Point := hT.1
  let : IsTopologicalAddGroup J2Local.toAffine.Point := hT.2.1
  let : Infinite (RationalPoints J2) := secondJacobian_infinite hSilvermanVII34
  have hr:0<(3:ℝ)^(-5:ℤ) := zpow_pos (by norm_num) _
  have hU:=secondCurveNeighborhood_mem_nhds hT.2.2 ((3:ℝ)^(-5:ℤ)) hr
  have hi:(secondPointToLocal ⁻¹' secondCurveNeighborhood ((3:ℝ)^(-5:ℤ))).Infinite :=
    infinite_preimage_nhds_of_injective secondPointToLocal secondPointToLocal_injective secondJacobianC0 hU
  have hf:(secondPointToLocal ⁻¹' secondCurveNeighborhood ((3:ℝ)^(-5:ℤ)) \
      {P:RationalPoints J2 | secondJacobianQuarticChart P}).Finite :=
    secondJacobianQuarticChart_complement_finite.subset (fun _ h=>h.2)
  have hg:(secondPointToLocal ⁻¹' secondCurveNeighborhood ((3:ℝ)^(-5:ℤ)) ∩
      {P:RationalPoints J2 | secondJacobianQuarticChart P}).Infinite := hi.inter_of_finite_sdiff hf
  have him:=hg.image (secondLocalToG2_injOn.mono inter_subset_right)
  apply him.mono
  rintro _ ⟨P,⟨hP,hchart⟩,rfl⟩
  cases P with
  | zero => exact hchart.elim
  | some x y h =>
    exact secondLocalToG2_mem_neighborhood x y h hchart
      (secondThetaNear3_of_padic_bound _ (secondCurveNeighborhood_some_bound _ x y h hP))

/-- Every point in this infinite class has the exact rational torsion claimed
in Remark 8.2, using the pointwise valuation theorem. -/
theorem secondThetaNeighborhood_torsion_exact(hMazur:MazurTorsionTheorem)
    (P:SecondFamily.G2Point ℚ)(hP:P∈secondThetaNeighborhoodSet):TorsionExact (SecondFamily.F P.W) := by
  obtain ⟨t,ht,hW,_,_⟩ := hP
  rw [hW]
  exact SecondFamily.F_theta_torsion_exact hMazur t ht

end
end Z2Z4Rank6
