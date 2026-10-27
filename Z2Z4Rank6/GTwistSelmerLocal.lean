module

public import Z2Z4Rank6.GTwistSelmerData
public import Z2Z4Rank6.TwistSelmerDataLocal
public import Z2Z4Rank6.SplitTwistPrimeConditions

@[expose] public section

/-!
# Necessary odd-prime conditions for the extra h-twist

Every condition is derived from the everywhere locally soluble
two-quadric covering. The finite matrix used later encodes these proved conditions.
Source: Jaswal, Proposition 7.2(b), DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.GTwistSelmer

noncomputable section

private theorem first_prime_facts (p : ℕ) (hp : p∈([11,13,29,53,113] : List ℕ)) :
    p.Prime ∧ (p:ℤ)^2∣r2 ∧ ¬(p:ℤ)∣r3 ∧ ¬(p:ℤ)∣r3*(r2-r3) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num [r2,r3,D,A,B]

private theorem second_prime_facts (p : ℕ) (hp : p∈([31,47,83,107] : List ℕ)) :
    p.Prime ∧ (p:ℤ)^2∣r3 ∧ ¬(p:ℤ)∣r2 ∧ ¬(p:ℤ)∣r2*(r2-r3) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> norm_num [r2,r3,D,A,B]

private theorem first_root_square (p : ℕ) [Fact p.Prime]
    (hp : p∈([11,13,29,53,113] : List ℕ)) : IsSquare (r3 : ZMod p) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨4,by norm_num [r3,D,B]; decide +kernel +revert⟩
  · exact ⟨1,by norm_num [r3,D,B]; decide +kernel +revert⟩
  · exact ⟨4,by norm_num [r3,D,B]; decide +kernel +revert⟩
  · exact ⟨14,by norm_num [r3,D,B]; decide +kernel +revert⟩
  · exact ⟨38,by norm_num [r3,D,B]; decide +kernel +revert⟩

private theorem second_root_square (p : ℕ) [Fact p.Prime]
    (hp : p∈([31,47,83,107] : List ℕ)) : IsSquare (r2 : ZMod p) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨6,by norm_num [r2,D,A]; decide +kernel +revert⟩
  · exact ⟨8,by norm_num [r2,D,A]; decide +kernel +revert⟩
  · exact ⟨29,by norm_num [r2,D,A]; decide +kernel +revert⟩
  · exact ⟨34,by norm_num [r2,D,A]; decide +kernel +revert⟩

theorem first_square_condition (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (p : ℕ) [Fact p.Prime] (hp : p∈([11,13,29,53,113] : List ℕ)) :
    IsSquare (d.2.2 : ZMod p) := by
  obtain ⟨_,hr2,hr3,hrange⟩ := first_prime_facts p hp
  rcases hd with ⟨hs1,hs2,hs3,_,_,hd3,hsq,hlocal⟩
  exact splitCover_third_isSquare_of_first_square d r2 r3 hs1 hs2 hs3 hsq hr2
    (first_root_square p hp)
    (fun hz => hr3 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    (fun hh => hrange (hh.trans hd3)) hlocal

theorem second_square_condition (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (p : ℕ) [Fact p.Prime] (hp : p∈([31,47,83,107] : List ℕ)) :
    IsSquare (d.2.1 : ZMod p) := by
  obtain ⟨_,hr3,hr2,hrange⟩ := second_prime_facts p hp
  rcases hd with ⟨hs1,hs2,hs3,_,hd2,_,hsq,hlocal⟩
  exact splitCover_second_isSquare_of_third_square d r2 r3 hs1 hs2 hs3 hsq hr3
    (second_root_square p hp)
    (fun hz => hr2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz))
    (fun hh => hrange (hh.trans hd2)) hlocal

theorem difference_square_condition (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (p : ℕ) [Fact p.Prime] (hp : p∈([7,593,787,1433] : List ℕ)) :
    IsSquare ((if (p:ℤ)∣d.2.1 then -d.1*r2 else d.1 : ℤ) : ZMod p) := by
  have hf : (p:ℤ)∣r2-r3 ∧ ¬(p:ℤ)^2∣r2-r3 ∧ ¬(p:ℤ)∣r2*r3 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num [r2,r3,D,A,B]
  rcases hd with ⟨hs1,hs2,hs3,hd1,_,_,hsq,hlocal⟩
  exact TwistSelmer.first_mixed_isSquare_of_simple_difference d r2 r3 hs1 hs2 hs3 hsq
    hf.1 hf.2.1 (fun hh => hf.2.2 (hh.trans hd1)) hlocal

theorem common_prime_conditions (d : ECFullTriple) (hd : d∈fullTwoSelmerTriples r2 r3)
    (p : ℕ) [Fact p.Prime] (hp : p∈([1291,2083] : List ℕ)) :
    IsSquare ((SplitTwistPrime.unitPart p d.1*
      (if (p:ℤ)∣d.1 then -(r3/(p:ℤ)) else 1) : ℤ) : ZMod p) ∧
    IsSquare ((SplitTwistPrime.unitPart p d.2.1*
      (if (p:ℤ)∣d.1 then (r2/(p:ℤ))*(r2/(p:ℤ)-r3/(p:ℤ)) else 1)*
      (if (p:ℤ)∣d.2.1 then r2/(p:ℤ) else 1) : ℤ) : ZMod p) := by
  have hf : r2=(p:ℤ)*(r2/(p:ℤ)) ∧ r3=(p:ℤ)*(r3/(p:ℤ)) ∧
      ((r2/(p:ℤ) : ℤ) : ZMod p)≠0 ∧ ((r3/(p:ℤ) : ℤ) : ZMod p)≠0 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> norm_num [r2,r3,D,A,B] <;> decide +kernel +revert
  have hsqmod : IsSquare (((r2/(p:ℤ))*(r3/(p:ℤ)) : ℤ) : ZMod p) := by
    refine ⟨(((D/(p:ℤ))*A*B : ℤ) : ZMod p),?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl <;> norm_num [r2,r3,D,A,B]
  rcases hd with ⟨hs1,hs2,hs3,_,_,_,hsq,hlocal⟩
  exact SplitTwistPrime.shared_prime_square_conditions d r2 r3 (r2/(p:ℤ)) (r3/(p:ℤ))
    hs1 hs2 hs3 hf.1 hf.2.1 hf.2.2.1 hf.2.2.2 hsqmod hsq hlocal

end
end Z2Z4Rank6.GTwistSelmer
