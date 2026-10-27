module

public import Z2Z4Rank6.GJacobianData
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
/-! Rational squareclass vector space for J_G, Proposition 7.2 (a). -/
namespace Z2Z4Rank6
local instance gJacobianVectorOneLtTwo : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
set_option maxHeartbeats 5000000

def gJacobianRepresentatives : Fin 4 → ℚ × ℚ :=
  ![(-21,15),(-231,165),(-11,22),(-1,74)]
noncomputable def gJacobianPairClass (q:ℚ×ℚ):RatSquareClassAdd×RatSquareClassAdd :=
  (squareClass q.1,squareClass q.2)
noncomputable def gJacobianBasis : Fin 4 → RatSquareClassAdd×RatSquareClassAdd :=
  fun i=>gJacobianPairClass (gJacobianRepresentatives i)
def gJacobianSurvivorTriple : Fin 16 → ECFullTriple :=
  ![(-231, 165, -35),(-231, 6105, -1295),(-21, 15, -35),(-21, 555, -1295),(-11, 22, -2),(-11, 814, -74),(-1, 2, -2),(-1, 74, -74),(1, 1, 1),(1, 37, 37),(11, 11, 1),(11, 407, 37),(21, 30, 70),(21, 1110, 2590),(231, 330, 70),(231, 12210, 2590)]
def gJacobianCoefficients : Fin 16 → Fin 4 → ZMod 2 :=
  ![![0,1,0,0],![1,0,1,1],![1,0,0,0],![0,1,1,1],![0,0,1,0],![1,1,0,1],![1,1,1,0],![0,0,0,1],![0,0,0,0],![1,1,1,1],![1,1,0,0],![0,0,1,1],![0,1,1,0],![1,0,0,1],![1,0,1,0],![0,1,0,1]]
def gJacobianRawProducts : Fin 16 → ℚ×ℚ :=
  ![(-231, 165),(-231, 24420),(-21, 15),(-2541, 268620),(-11, 22),(-4851, 183150),(-53361, 54450),(-1, 74),(1, 1),(53361, 4029300),(4851, 2475),(11, 1628),(2541, 3630),(21, 1110),(231, 330),(231, 12210)]
def gJacobianSquareFactors : Fin 16 → ℚ×ℚ :=
  ![(1,1),(1,2),(1,1),(11,22),(1,1),(21,15),(231,165),(1,1),(1,1),(231,330),(21,15),(1,2),(11,11),(1,1),(1,1),(1,1)]

private theorem class_pair_prod {ι:Type*} [DecidableEq ι] (s:Finset ι)
    (q:ι→ℚ×ℚ) (hq:∀i,(q i).1≠0 ∧ (q i).2≠0):
    gJacobianPairClass (∏i∈s,(q i).1,∏i∈s,(q i).2)=∑i∈s,gJacobianPairClass (q i) := by
  induction s using Finset.induction_on with
  | empty => simp [gJacobianPairClass,squareClass_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.sum_insert ha,←ih]
    apply Prod.ext
    · exact squareClass_mul _ _ (hq a).1 (Finset.prod_ne_zero_iff.mpr (fun i _=>(hq i).1))
    · exact squareClass_mul _ _ (hq a).2 (Finset.prod_ne_zero_iff.mpr (fun i _=>(hq i).2))

private theorem class_pair_prod_pow {ι:Type*}[Fintype ι][DecidableEq ι]
    (q:ι→ℚ×ℚ) (hq:∀i,(q i).1≠0 ∧ (q i).2≠0) (c:ι→ZMod 2):
    gJacobianPairClass (∏i,(q i).1^(c i).val,∏i,(q i).2^(c i).val)=
      ∑i,c i • gJacobianPairClass (q i) := by
  rw [class_pair_prod Finset.univ
    (fun i=>((q i).1^(c i).val,(q i).2^(c i).val))
    (fun i=>⟨pow_ne_zero _ (hq i).1,pow_ne_zero _ (hq i).2⟩)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [gJacobianPairClass,squareClass_pow _ _ (hq i).1,squareClass_pow _ _ (hq i).2]
  change (c i).val • (squareClass (q i).1,squareClass (q i).2)=
    c i • (squareClass (q i).1,squareClass (q i).2)
  simpa only [ZMod.natCast_zmod_val] using
    (Nat.cast_smul_eq_nsmul (ZMod 2) (c i).val (squareClass (q i).1,squareClass (q i).2)).symm

private theorem gJacobian_raw_products (i:Fin 16):
    gJacobianRawProducts i=(∏j,(gJacobianRepresentatives j).1^(gJacobianCoefficients i j).val,
      ∏j,(gJacobianRepresentatives j).2^(gJacobianCoefficients i j).val) := by
  fin_cases i <;> norm_num [gJacobianRawProducts,gJacobianRepresentatives,gJacobianCoefficients,
    Fin.prod_univ_succ,ZMod.val_one 2]

private theorem gJacobian_square_factors (i:Fin 16):
    (gJacobianRawProducts i).1=(gJacobianSurvivorTriple i).1*(gJacobianSquareFactors i).1^2 ∧
    (gJacobianRawProducts i).2=(gJacobianSurvivorTriple i).2.1*(gJacobianSquareFactors i).2^2 := by
  fin_cases i <;> norm_num [gJacobianRawProducts,gJacobianSurvivorTriple,gJacobianSquareFactors]

theorem gJacobian_survivor_class_formula (i:Fin 16):
    gJacobianPairClass ((gJacobianSurvivorTriple i).1,(gJacobianSurvivorTriple i).2.1)=
      Fintype.linearCombination (ZMod 2) gJacobianBasis (gJacobianCoefficients i) := by
  have hprod:=class_pair_prod_pow gJacobianRepresentatives
    (by intro j;fin_cases j <;> norm_num [gJacobianRepresentatives]) (gJacobianCoefficients i)
  rw [←gJacobian_raw_products i] at hprod
  have hclass:gJacobianPairClass (gJacobianRawProducts i)=
      gJacobianPairClass ((gJacobianSurvivorTriple i).1,(gJacobianSurvivorTriple i).2.1) := by
    apply Prod.ext
    · apply squareClass_eq_of_factor _ _ (gJacobianSquareFactors i).1
      · fin_cases i <;> norm_num [gJacobianRawProducts]
      · fin_cases i <;> norm_num [gJacobianSurvivorTriple]
      · fin_cases i <;> norm_num [gJacobianSquareFactors]
      · exact (gJacobian_square_factors i).1
    · apply squareClass_eq_of_factor _ _ (gJacobianSquareFactors i).2
      · fin_cases i <;> norm_num [gJacobianRawProducts]
      · fin_cases i <;> norm_num [gJacobianSurvivorTriple]
      · fin_cases i <;> norm_num [gJacobianSquareFactors]
      · exact (gJacobian_square_factors i).2
  exact hclass.symm.trans hprod

theorem gJacobianSurvivorTriple_mem_iff (d:ECFullTriple):
    d∈gJacobianSurvivors ↔ ∃i,gJacobianSurvivorTriple i=d := by
  simp only [gJacobianSurvivors,List.mem_cons,List.not_mem_nil,or_false,
    gJacobianSurvivorTriple,Fin.exists_fin_succ,Fin.exists_fin_zero]
  tauto

theorem gJacobianCoefficients_surjective:Function.Surjective gJacobianCoefficients := by decide +kernel

private theorem valuation_nat_zero_or_one {p n : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (hp2 : ¬p ^ 2 ∣ n) :
    padicValNat p n = if p ∣ n then 1 else 0 := by
  split_ifs with hdiv
  · have hlow : 1 ≤ padicValNat p n := by
      apply (padicValNat_dvd_iff_le hn).1
      simpa only [pow_one] using hdiv
    have hhigh : ¬2 ≤ padicValNat p n := by
      intro hh
      exact hp2 ((padicValNat_dvd_iff_le hn).2 hh)
    omega
  · exact padicValNat.eq_zero_of_not_dvd hdiv

local instance gJacobianVectorPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance gJacobianVectorPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance gJacobianVectorPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance gJacobianVectorPrimeThirtySeven : Fact (Nat.Prime 37) := ⟨by decide⟩

noncomputable def gJacobianParity : (RatSquareClassAdd × RatSquareClassAdd) →+ (Fin 4 → ZMod 2) where
  toFun q := ![squareClassValuation 37 q.2,squareClassValuation 2 q.2,
    squareClassValuation 11 q.1,squareClassValuation 7 q.1]
  map_zero' := by ext i;fin_cases i <;> simp
  map_add' q r := by ext i;fin_cases i <;> simp

def gJacobianParityVectors : Fin 4 → Fin 4 → ZMod 2 :=
  ![![0,0,0,1],![0,0,1,1],![0,1,1,0],![1,1,0,0]]

theorem gJacobian_parity_values (i : Fin 4) :
    gJacobianParity (gJacobianBasis i)=gJacobianParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [gJacobianParity,gJacobianBasis,gJacobianPairClass,gJacobianRepresentatives,
      gJacobianParityVectors,AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals norm_num
  all_goals rw [squareClassValuation_apply _ _ (by norm_num)]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem gJacobian_basis_independent : LinearIndependent (ZMod 2) gJacobianBasis := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑i,n i • gJacobianParityVectors i=0 := by
    have hh:=congrArg gJacobianParity hn
    simpa only [map_sum,ZMod.map_smul,gJacobian_parity_values,map_zero] using hh
  have h0:=congrFun hm 0
  have h1:=congrFun hm 1
  have h2:=congrFun hm 2
  have h3:=congrFun hm 3
  norm_num [Fin.sum_univ_succ,gJacobianParityVectors] at h0 h1 h2 h3
  intro i
  fin_cases i <;> simp_all

noncomputable def gJacobianSelmerSpace : Submodule (ZMod 2) (RatSquareClassAdd×RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (Set.range gJacobianBasis)

theorem gJacobianSelmerSpace_finrank : Module.finrank (ZMod 2) gJacobianSelmerSpace=4 := by
  unfold gJacobianSelmerSpace
  convert finrank_span_eq_card gJacobian_basis_independent using 1
  simp only [Fintype.card_fin]

theorem gJacobian_survivor_classes_eq_space :
    (fun d:ECFullTriple=>gJacobianPairClass ((d.1:ℚ),(d.2.1:ℚ))) ''
      (gJacobianSurvivors.toFinset:Set ECFullTriple)=(gJacobianSelmerSpace:Set _) := by
  rw [gJacobianSelmerSpace,←Fintype.range_linearCombination]
  ext q
  constructor
  · rintro ⟨d,hd,rfl⟩
    have hm:d∈gJacobianSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using hd
    obtain ⟨i,rfl⟩ := (gJacobianSurvivorTriple_mem_iff d).mp hm
    exact ⟨gJacobianCoefficients i,(gJacobian_survivor_class_formula i).symm⟩
  · rintro ⟨c,rfl⟩
    obtain ⟨i,rfl⟩ := gJacobianCoefficients_surjective c
    refine ⟨gJacobianSurvivorTriple i,?_,gJacobian_survivor_class_formula i⟩
    simpa only [Finset.mem_coe,List.mem_toFinset] using
      (gJacobianSurvivorTriple_mem_iff (gJacobianSurvivorTriple i)).mpr ⟨i,rfl⟩

end Z2Z4Rank6
