module

public import Z2Z4Rank6.SecondJacobianSelmerData

@[expose] public section

namespace Z2Z4Rank6.SecondJacobianSelmer
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem signed_divisor_mem (N : ℕ) (hn : N≠0) (pos : List ℕ) (signed : List ℤ)
    (hdivs : N.divisors=pos.toFinset)
    (hsigns : ∀n∈pos,(n:ℤ)∈signed ∧ -(n:ℤ)∈signed)
    (d:ℤ) (hd:d∣(N:ℤ)) : d∈signed := by
  have hm : d.natAbs∈N.divisors := Nat.mem_divisors.mpr ⟨Int.dvd_natCast.mp hd,hn⟩
  rw [hdivs,List.mem_toFinset] at hm
  have hp := hsigns d.natAbs hm
  rcases Int.natAbs_eq d with h | h
  · exact h ▸ hp.1
  · exact h ▸ hp.2

private theorem positive1_divisors : (100947:ℕ).divisors=positive1.toFinset := by
  rw [show (100947:ℕ)=3*7*11*19*23 by decide]
  simp only [Nat.divisors_mul]
  rw [(by decide:Nat.Prime 3).divisors,(by decide:Nat.Prime 7).divisors,
    (by decide:Nat.Prime 11).divisors,(by decide:Nat.Prime 19).divisors,
    (by decide:Nat.Prime 23).divisors]
  decide +kernel

private theorem divisorList_toFinset (ps:List ℕ) (hp:∀p∈ps,Nat.Prime p) :
    (divisorList ps).toFinset=ps.prod.divisors := by
  induction ps with
  | nil => simp [divisorList]
  | cons p ps ih =>
    have hpp:=hp p (by simp)
    have hps:∀q∈ps,Nat.Prime q:=fun q h=>hp q (by simp [h])
    rw [List.prod_cons,Nat.divisors_mul,hpp.divisors,←ih hps]
    ext n
    simp [divisorList,Finset.mem_mul,eq_comm,or_and_right,exists_or]

private theorem positive2_divisors : (141885040110:ℕ).divisors=positive2.toFinset := by
  have h := (divisorList_toFinset [2,3,5,11,17,19,29,197,233]
    (by decide +kernel)).symm
  have he : ([2,3,5,11,17,19,29,197,233]:List ℕ).prod=141885040110 := by decide
  rw [he] at h
  exact h

private theorem signs2 : ∀n∈positive2,(n:ℤ)∈signed2 ∧ -(n:ℤ)∈signed2 := by
  have he : signed2=positive2.map (fun n:ℕ=>(n:ℤ))++positive2.map (fun n:ℕ=>-(n:ℤ)) := by
    decide +kernel
  intro n hn
  rw [he]
  exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨n,hn,rfl⟩),
    List.mem_append_right _ (List.mem_map.mpr ⟨n,hn,rfl⟩)⟩

theorem support_lists (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples A B) :
    d.1∈signed1 ∧ d.2.1∈signed2 := by
  have hs := support_radicals d hd
  constructor
  · exact signed_divisor_mem 100947 (by decide) positive1 signed1 positive1_divisors
      (by decide +kernel) d.1 hs.1
  · exact signed_divisor_mem 141885040110 (by decide) positive2 signed2 positive2_divisors
      signs2 d.2.1 hs.2.1

local instance supportPrime3 : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance supportPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance supportPrime19 : Fact (Nat.Prime 19) := ⟨by decide⟩

theorem necessary_sharedParity (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples A B) :
    SharedParity d.1 d.2.1 :=
  ⟨pair_parity d hd (by norm_num [radical3]),
    pair_parity d hd (by norm_num [radical3]),
    pair_parity d hd (by norm_num [radical3])⟩

end Z2Z4Rank6.SecondJacobianSelmer
