module

public import Z2Z4Rank6.TwistSelmerDataConstraints
public import Z2Z4Rank6.TwistSelmerDataLocal
public import Z2Z4Rank6.SplitRealConditions

@[expose] public section

/-!
# Necessary character constraints for covering triples

Generic adapters from the proved local equations to the precise binary rows
used in the three twist certificates of Jaswal, Proposition 5.2,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6.TwistSelmer

open scoped BigOperators
noncomputable section

def rootProduct (r2 r3 : ℤ) : Fin 3 → ℤ :=
  ![r2*r3,r2*(r2-r3),r3*(r2-r3)]

theorem coefficient_squarefree_of_mem (d : ECFullTriple) (r2 r3 : ℤ)
    (hd : d∈fullTwoSelmerTriples r2 r3) (c : Fin 3) : Squarefree (coefficient d c) := by
  fin_cases c
  · exact hd.1
  · exact hd.2.1
  · exact hd.2.2.1

theorem coefficient_divisor_of_mem (d : ECFullTriple) (r2 r3 : ℤ)
    (hd : d∈fullTwoSelmerTriples r2 r3) (c : Fin 3) : coefficient d c∣rootProduct r2 r3 c := by
  fin_cases c
  · exact hd.2.2.2.1
  · exact hd.2.2.2.2.1
  · exact hd.2.2.2.2.2.1

theorem coefficient_support_bound {s : ℕ} (ps : Fin s → ℕ) (d : ECFullTriple) (r2 r3 : ℤ)
    (k : ℕ) (hp : ∀ c, rootProduct r2 r3 c∣((∏ i, ps i : ℕ) : ℤ)^k)
    (hd : d∈fullTwoSelmerTriples r2 r3) (c : Fin 3) :
    (coefficient d c).natAbs∣(∏ i, ps i)^k := by
  apply Int.dvd_natCast.mp
  simpa only [Nat.cast_pow] using (coefficient_divisor_of_mem d r2 r3 hd c).trans (hp c)

theorem zero_constraint_of_nondiv {s : ℕ} (ps : Fin s → ℕ)
    (d : ECFullTriple) (c : Fin 3) (j : Fin s) (hn : ¬(ps j : ℤ)∣coefficient d c) :
    constraintValue ps d (.zero c j)=0 := by
  simp [constraintValue,primeBit,hn]

theorem product_constraint_of_mem {s : ℕ} (ps : Fin s → ℕ)
    (hprime : ∀ i, (ps i).Prime) (d : ECFullTriple) (r2 r3 : ℤ)
    (hd : d∈fullTwoSelmerTriples r2 r3) (j : Fin s) :
    constraintValue ps d (.product j)=0 := by
  let : Fact (ps j).Prime := ⟨hprime j⟩
  have h := SplitPrimeBits.square_product_parity (p:=ps j) d.1 d.2.1 d.2.2
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.2.2.2.1
  change (∑ c : Fin 3, primeBit (ps j) (coefficient d c))=0
  have hsum : (∑ c : Fin 3, primeBit (ps j) (coefficient d c))=
      primeBit (ps j) d.1+(primeBit (ps j) d.2.1+primeBit (ps j) d.2.2) := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    rfl
  rw [hsum]
  by_cases h1 : (ps j : ℤ)∣d.1 <;>
    by_cases h2 : (ps j : ℤ)∣d.2.1 <;>
    by_cases h3 : (ps j : ℤ)∣d.2.2
  all_goals simp only [primeBit,h1,h2,h3,ite_true,ite_false] at h ⊢
  all_goals first | decide +kernel | exact False.elim (by revert h; decide +kernel)

theorem first_square_character {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr2 : (ps j : ℤ)^2∣r2) (hr3 : IsSquare (r3 : ZMod (ps j)))
    (hr30 : (r3 : ZMod (ps j))≠0) (hd3 : ¬(ps j : ℤ)∣d.2.2) :
    constraintValue ps d (.character 2 j ![0,0,0])=0 := by
  have h := splitCover_third_isSquare_of_first_square d r2 r3 hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.2.2.2.1 hr2 hr3 hr30 hd3 hd.2.2.2.2.2.2.2
  have h' := (modularParity_eq_zero_iff (ps j) d.2.2).mpr h
  simpa [constraintValue,Fin.sum_univ_succ,coefficient,SplitTwistPrime.unitPart,hd3] using h'

theorem third_square_character {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr3 : (ps j : ℤ)^2∣r3) (hr2 : IsSquare (r2 : ZMod (ps j)))
    (hr20 : (r2 : ZMod (ps j))≠0) (hd2 : ¬(ps j : ℤ)∣d.2.1) :
    constraintValue ps d (.character 1 j ![0,0,0])=0 := by
  have h := splitCover_second_isSquare_of_third_square d r2 r3 hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.2.2.2.1 hr3 hr2 hr20 hd2 hd.2.2.2.2.2.2.2
  have h' := (modularParity_eq_zero_iff (ps j) d.2.1).mpr h
  simpa [constraintValue,Fin.sum_univ_succ,coefficient,SplitTwistPrime.unitPart,hd2] using h'

theorem first_nonsquare_zero {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 R : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr2 : r2=(ps j : ℤ)^2*R) (hR : ¬(ps j : ℤ)∣R)
    (hd3 : ¬(ps j : ℤ)∣d.2.2) (hr3 : ¬IsSquare (r3 : ZMod (ps j))) :
    constraintValue ps d (.zero 0 j)=0 := by
  apply zero_constraint_of_nondiv
  exact first_coefficient_unramified d r2 r3 R hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.2.2.2.1
    hr2 hR hd3 hr3 hd.2.2.2.2.2.2.2

theorem third_nonsquare_zero {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 R : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr3 : r3=(ps j : ℤ)^2*R) (hR : ¬(ps j : ℤ)∣R)
    (hd2 : ¬(ps j : ℤ)∣d.2.1) (hr2 : ¬IsSquare (r2 : ZMod (ps j))) :
    constraintValue ps d (.zero 0 j)=0 := by
  apply zero_constraint_of_nondiv
  exact first_coefficient_unramified_of_third_root d r2 r3 R hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.2.2.2.1 hr3 hR hd2 hr2 hd.2.2.2.2.2.2.2

theorem simple_difference_character {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr : (ps j : ℤ)∣r2-r3) (hrsq : ¬(ps j : ℤ)^2∣r2-r3)
    (hr20 : (r2 : ZMod (ps j))≠0) (hd1 : ¬(ps j : ℤ)∣d.1) :
    constraintValue ps d (.character 0 j (fun c => modularParity (ps j) (![1,-r2,1] c)))=0 := by
  have h := first_mixed_isSquare_of_simple_difference d r2 r3 hd.1 hd.2.1 hd.2.2.1
    hd.2.2.2.2.2.2.1 hr hrsq hd1 hd.2.2.2.2.2.2.2
  apply character_constraint_of_selected_square ps d 0 j hd.1 ![1,-r2,1]
  · intro c
    fin_cases c
    · simp
    · simpa using neg_ne_zero.mpr hr20
    · simp
  · by_cases h2 : (ps j : ℤ)∣d.2.1
    · simpa [Fin.prod_univ_succ,Fin.prod_univ_two,coefficient,
        SplitTwistPrime.unitPart,hd1,h2,mul_neg] using h
    · simpa [Fin.prod_univ_succ,Fin.prod_univ_two,coefficient,
        SplitTwistPrime.unitPart,hd1,h2] using h

theorem shared_prime_characters {s : ℕ} (ps : Fin s → ℕ) (j : Fin s) [Fact (ps j).Prime]
    (d : ECFullTriple) (r2 r3 R2 R3 : ℤ) (hd : d∈fullTwoSelmerTriples r2 r3)
    (hr2 : r2=(ps j : ℤ)*R2) (hr3 : r3=(ps j : ℤ)*R3)
    (hR2 : (R2 : ZMod (ps j))≠0) (hR3 : (R3 : ZMod (ps j))≠0)
    (hRdiff : ((R2-R3 : ℤ) : ZMod (ps j))≠0)
    (hRR : IsSquare ((R2*R3 : ℤ) : ZMod (ps j))) :
    constraintValue ps d (.character 0 j (fun c => modularParity (ps j) (![-R3,1,1] c)))=0 ∧
    constraintValue ps d (.character 1 j (fun c => modularParity (ps j) (![R2*(R2-R3),R2,1] c)))=0 := by
  obtain ⟨h1,h2⟩ := SplitTwistPrime.shared_prime_square_conditions d r2 r3 R2 R3
    hd.1 hd.2.1 hd.2.2.1 hr2 hr3 hR2 hR3 hRR hd.2.2.2.2.2.2.1 hd.2.2.2.2.2.2.2
  constructor
  · apply character_constraint_of_selected_square ps d 0 j hd.1 ![-R3,1,1]
    · intro c
      fin_cases c
      · simpa using neg_ne_zero.mpr hR3
      · simp
      · simp
    · by_cases ha : (ps j : ℤ)∣d.1 <;> by_cases hb : (ps j : ℤ)∣d.2.1
      all_goals simpa [Fin.prod_univ_succ,Fin.prod_univ_two,coefficient,ha,hb] using h1
  · apply character_constraint_of_selected_square ps d 1 j hd.2.1 ![R2*(R2-R3),R2,1]
    · intro c
      fin_cases c
      · change ((R2*(R2-R3) : ℤ) : ZMod (ps j))≠0
        simpa only [Int.cast_mul] using mul_ne_zero hR2 hRdiff
      · exact hR2
      · simp
    · by_cases ha : (ps j : ℤ)∣d.1 <;> by_cases hb : (ps j : ℤ)∣d.2.1
      all_goals simpa [Fin.prod_univ_succ,Fin.prod_univ_two,coefficient,ha,hb,mul_assoc] using h2


end
end Z2Z4Rank6.TwistSelmer
