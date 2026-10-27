module

public import Z2Z4Rank6.ECFullSelmerModel
public import Z2Z4Rank6.ECFullSelmerData
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-!
# The three-dimensional space of the explicit full two-descent classes

The basis and distinguishing valuations use rational squareclasses.
Source: Jaswal, Lemma 4.1(b), DOI 10.5281/zenodo.23437117; the finite local
certificate is in ECFullSelmerCertificate.
-/
namespace Z2Z4Rank6

noncomputable def ecPairSquareClass (a b : ℚ) : RatSquareClassAdd × RatSquareClassAdd :=
  (squareClass a,squareClass b)

noncomputable def ecFullBasis : Fin 3 → RatSquareClassAdd × RatSquareClassAdd :=
  ![ecPairSquareClass (-6) 3,ecPairSquareClass (-1) 5,ecPairSquareClass (-66) 15]

local instance ecFullVectorPrimeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance ecFullVectorPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance ecFullVectorPrimeEleven : Fact (Nat.Prime 11) := ⟨by decide⟩

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

noncomputable def ecFullParity : (RatSquareClassAdd × RatSquareClassAdd) →+ (Fin 3 → ZMod 2) where
  toFun q := ![squareClassValuation 11 q.1,squareClassValuation 2 q.1,
    squareClassValuation 5 q.2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' q r := by ext i; fin_cases i <;> simp

def ecFullParityVectors : Fin 3 → Fin 3 → ZMod 2 :=
  ![![0,1,0],![0,0,1],![1,1,1]]

theorem ecFull_parity_values (i : Fin 3) :
    ecFullParity (ecFullBasis i) = ecFullParityVectors i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp only [ecFullParity,ecFullBasis,ecPairSquareClass,ecFullParityVectors,
      AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  all_goals norm_num
  all_goals rw [squareClassValuation_apply _ _ (by norm_num)]
  all_goals norm_num [padicValRat_def,padicValInt]
  all_goals try rw [valuation_nat_zero_or_one (by decide) (by decide)]
  all_goals norm_num

theorem ecFull_basis_independent : LinearIndependent (ZMod 2) ecFullBasis := by
  apply Fintype.linearIndependent_iff.mpr
  intro n hn
  have hm : ∑ i, n i • ecFullParityVectors i = 0 := by
    have hh := congrArg ecFullParity hn
    simpa only [map_sum,ZMod.map_smul,ecFull_parity_values,map_zero] using hh
  have h0 := congrFun hm 0
  have h1 := congrFun hm 1
  have h2 := congrFun hm 2
  norm_num [Fin.sum_univ_succ,ecFullParityVectors] at h0 h1 h2
  intro i
  fin_cases i <;> simp_all

noncomputable def ecFullSelmerSpace : Submodule (ZMod 2)
    (RatSquareClassAdd × RatSquareClassAdd) :=
  Submodule.span (ZMod 2) (Set.range ecFullBasis)

theorem ecFullSelmerSpace_finrank : Module.finrank (ZMod 2) ecFullSelmerSpace = 3 := by
  unfold ecFullSelmerSpace
  convert finrank_span_eq_card ecFull_basis_independent using 1
  simp only [Fintype.card_fin]

private theorem pairClass_mul (a b c d : ℚ) (ha : a≠0) (hb : b≠0)
    (hc : c≠0) (hd : d≠0) :
    ecPairSquareClass (a*c) (b*d) = ecPairSquareClass a b + ecPairSquareClass c d := by
  ext <;> simp only [ecPairSquareClass,Prod.fst_add,Prod.snd_add,squareClass_mul _ _ ha hc,
    squareClass_mul _ _ hb hd]

private theorem ecFull_PT :
    ecFullBasis 0 + ecFullBasis 1 = ecPairSquareClass 6 15 := by
  have h := (pairClass_mul (-6) 3 (-1) 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  norm_num at h
  exact h

private theorem ecFull_PQ :
    ecFullBasis 0 + ecFullBasis 2 = ecPairSquareClass 11 5 := by
  have h := (pairClass_mul (-6) 3 (-66) 15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  norm_num at h
  rw [show ecPairSquareClass 396 45 = ecPairSquareClass 11 5 by
    apply Prod.ext
    · exact squareClass_eq_of_factor 396 11 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact squareClass_eq_of_factor 45 5 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at h
  exact h

private theorem ecFull_TQ :
    ecFullBasis 1 + ecFullBasis 2 = ecPairSquareClass 66 3 := by
  have h := (pairClass_mul (-1) 5 (-66) 15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  norm_num at h
  rw [show ecPairSquareClass 66 75 = ecPairSquareClass 66 3 by
    apply Prod.ext
    · rfl
    · exact squareClass_eq_of_factor 75 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at h
  exact h

private theorem ecFull_PTQ :
    ecFullBasis 0 + ecFullBasis 1 + ecFullBasis 2 = ecPairSquareClass (-11) 1 := by
  rw [ecFull_PT]
  have h := (pairClass_mul 6 15 (-66) 15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
  norm_num at h
  rw [show ecPairSquareClass (-396) 225 = ecPairSquareClass (-11) 1 by
    apply Prod.ext
    · exact squareClass_eq_of_factor (-396) (-11) 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact squareClass_eq_of_factor 225 1 15 (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at h
  exact h

def ecFullSurvivorTriple : Fin 8 → ECFullTriple :=
  ![(-66,15,-110),(-11,1,-11),(-6,3,-2),(-1,5,-5),
    (1,1,1),(6,15,10),(11,5,55),(66,3,22)]

def ecFullCoefficients : Fin 8 → Fin 3 → ZMod 2 :=
  ![![0,0,1],![1,1,1],![1,0,0],![0,1,0],
    ![0,0,0],![1,1,0],![1,0,1],![0,1,1]]

theorem ecFullSurvivorTriple_mem_iff (d : ECFullTriple) :
    d ∈ ecFullSurvivors ↔ ∃ i, ecFullSurvivorTriple i = d := by
  simp only [ecFullSurvivors,List.mem_cons,List.not_mem_nil,or_false,
    ecFullSurvivorTriple,Fin.exists_fin_succ,Fin.exists_fin_zero]
  tauto

theorem ecFull_survivor_class_formula (i : Fin 8) :
    ecPairSquareClass (ecFullSurvivorTriple i).1 (ecFullSurvivorTriple i).2.1 =
      Fintype.linearCombination (ZMod 2) ecFullBasis (ecFullCoefficients i) := by
  fin_cases i <;>
    norm_num [ecFullSurvivorTriple,ecFullCoefficients,Fintype.linearCombination_apply,
      Fin.sum_univ_succ]
  · rfl
  · exact ecFull_PTQ.symm.trans (by abel)
  · rfl
  · rfl
  · exact Prod.ext squareClass_one squareClass_one
  · exact ecFull_PT.symm
  · exact ecFull_PQ.symm
  · exact ecFull_TQ.symm

theorem ecFullCoefficients_surjective : Function.Surjective ecFullCoefficients := by
  decide +kernel

theorem ecFull_survivor_classes_eq_space :
    (fun d : ECFullTriple => ecPairSquareClass (d.1 : ℚ) (d.2.1 : ℚ)) ''
      (ecFullSurvivors.toFinset : Set ECFullTriple) = (ecFullSelmerSpace : Set _) := by
  rw [ecFullSelmerSpace,←Fintype.range_linearCombination]
  ext q
  constructor
  · rintro ⟨d,hd,rfl⟩
    have hm : d ∈ ecFullSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using hd
    obtain ⟨i,rfl⟩ := (ecFullSurvivorTriple_mem_iff d).mp hm
    exact ⟨ecFullCoefficients i,(ecFull_survivor_class_formula i).symm⟩
  · rintro ⟨c,rfl⟩
    obtain ⟨i,rfl⟩ := ecFullCoefficients_surjective c
    refine ⟨ecFullSurvivorTriple i,?_,ecFull_survivor_class_formula i⟩
    simpa only [Finset.mem_coe,List.mem_toFinset] using
      (ecFullSurvivorTriple_mem_iff (ecFullSurvivorTriple i)).mpr ⟨i,rfl⟩

end Z2Z4Rank6
