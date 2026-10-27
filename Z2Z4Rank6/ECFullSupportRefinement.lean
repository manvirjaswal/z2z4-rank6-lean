import Z2Z4Rank6.ECFullSelmerLocal
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic

/-!
# Elementary support refinement in complete two-descent

The primitive p² argument uses only divisibility and the two quadrics.
It is valid also at 2. This supplies the refinement from the larger support
in Silverman X.1.4 to the individual root-difference products.
-/
namespace Z2Z4Rank6

private theorem prime_dvd_square {p a : ℤ} (hp : Prime p) (h : p ∣ a^2) : p ∣ a :=
  hp.dvd_of_dvd_pow h

private theorem square_dvd_square {p a : ℤ} (h : p ∣ a) : p^2 ∣ a^2 := pow_dvd_pow_of_dvd h 2

theorem splitCover_two_divisors_force_nonprimitive
    (p d1 d2 d3 r2 r3 a b c t : ℤ) (hp : Prime p)
    (hs1 : Squarefree d1) (hs2 : Squarefree d2)
    (h1 : p ∣ d1) (h2 : p ∣ d2) (h3 : ¬p ∣ d3)
    (hr2 : ¬p ∣ r2) (_hr3 : ¬p ∣ r3)
    (he1 : p^2 ∣ d2*b^2-d1*a^2-r2*t^2)
    (he2 : p^2 ∣ d3*c^2-d1*a^2-r3*t^2) :
    p ∣ a ∧ p ∣ b ∧ p ∣ c ∧ p ∣ t := by
  have hpp : p ∣ p^2 := dvd_pow_self p (by decide)
  have ht : p ∣ t := by
    have hh : p ∣ r2*t^2 := by
      have hd : p ∣ d2*b^2-d1*a^2 := dvd_sub (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_left h1 _)
      exact (dvd_sub_right hd).mp (hpp.trans he1)
    exact prime_dvd_square hp ((hp.dvd_or_dvd hh).resolve_left hr2)
  have hc : p ∣ c := by
    have hh : p ∣ d3*c^2 := by
      have hd : p ∣ d1*a^2+r3*t^2 := dvd_add (dvd_mul_of_dvd_left h1 _)
        (dvd_mul_of_dvd_right (dvd_pow ht (by decide : (2 : ℕ) ≠ 0)) _)
      have he : p ∣ d3*c^2-(d1*a^2+r3*t^2) := by convert hpp.trans he2 using 1; ring
      exact (dvd_sub_left hd).mp he
    exact prime_dvd_square hp ((hp.dvd_or_dvd hh).resolve_left h3)
  have ha : p ∣ a := by
    have hd : p^2 ∣ d3*c^2-r3*t^2 := dvd_sub
      (dvd_mul_of_dvd_right (square_dvd_square hc) _) (dvd_mul_of_dvd_right (square_dvd_square ht) _)
    have he : p^2 ∣ (d3*c^2-r3*t^2)-d1*a^2 := by convert he2 using 1; ring
    have hh : p^2 ∣ d1*a^2 := (dvd_sub_right hd).mp he
    exact prime_dvd_square hp (Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs1 (by simpa only [pow_two] using hh))
  have hb : p ∣ b := by
    have hd : p^2 ∣ d1*a^2+r2*t^2 := dvd_add
      (dvd_mul_of_dvd_right (square_dvd_square ha) _) (dvd_mul_of_dvd_right (square_dvd_square ht) _)
    have he : p^2 ∣ d2*b^2-(d1*a^2+r2*t^2) := by convert he1 using 1; ring
    have hh : p^2 ∣ d2*b^2 := (dvd_sub_left hd).mp he
    exact prime_dvd_square hp (Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hs2 (by simpa only [pow_two] using hh))
  exact ⟨ha,hb,hc,ht⟩

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

theorem squarefree_int_valuation {p : ℕ} [Fact p.Prime] (d : ℤ) (hs : Squarefree d) :
    padicValInt p d = if (p : ℤ) ∣ d then 1 else 0 := by
  have hn : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hs.ne_zero
  have hsN : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hs
  have hp2 : ¬ p^2 ∣ d.natAbs :=
    by simpa only [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp hsN) p (Fact.out : p.Prime)
  rw [padicValInt,valuation_nat_zero_or_one hn hp2]
  simp only [Int.natCast_dvd]

theorem squarefree_product_prime_parity {p : ℕ} [Fact p.Prime]
    (d1 d2 d3 : ℤ) (hs1 : Squarefree d1) (hs2 : Squarefree d2) (hs3 : Squarefree d3)
    (hsq : IsSquare (d1*d2*d3)) (h1 : (p : ℤ) ∣ d1) :
    ((p : ℤ) ∣ d2 ∧ ¬(p : ℤ) ∣ d3) ∨ (¬(p : ℤ) ∣ d2 ∧ (p : ℤ) ∣ d3) := by
  obtain ⟨n,hn⟩ := hsq
  have hn0 : n ≠ 0 := by
    intro hh
    rw [hh,mul_zero] at hn
    exact mul_ne_zero (mul_ne_zero hs1.ne_zero hs2.ne_zero) hs3.ne_zero hn
  have hv := congrArg (padicValInt p) hn
  rw [padicValInt.mul (mul_ne_zero hs1.ne_zero hs2.ne_zero) hs3.ne_zero,
    padicValInt.mul hs1.ne_zero hs2.ne_zero,padicValInt.mul hn0 hn0,
    squarefree_int_valuation d1 hs1,squarefree_int_valuation d2 hs2,
    squarefree_int_valuation d3 hs3,ite_eq_left h1] at hv
  by_cases h2 : (p : ℤ) ∣ d2 <;> by_cases h3 : (p : ℤ) ∣ d3
  · simp only [ite_eq_left h2,ite_eq_left h3] at hv
    omega
  · exact Or.inl ⟨h2,h3⟩
  · exact Or.inr ⟨h2,h3⟩
  · simp only [ite_eq_right h2,ite_eq_right h3] at hv
    omega

theorem splitCover_integral_normalization_general {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p]) (r2 : ℚ_[p]) (r3 : ℚ_[p])) :
    ∃ z : Fin 4 → ℤ_[p], (∃ i, z i = 1) ∧
      (d.2.1 : ℤ_[p])*(z 1)^2-(d.1 : ℤ_[p])*(z 0)^2=(r2 : ℤ_[p])*(z 3)^2 ∧
      (d.2.2 : ℤ_[p])*(z 2)^2-(d.1 : ℤ_[p])*(z 0)^2=(r3 : ℤ_[p])*(z 3)^2 := by
  classical
  obtain ⟨w,hnonzero,h1,h2⟩ := h
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖w j‖)
    Finset.univ_nonempty
  have hmax : ∀ j, ‖w j‖ ≤ ‖w i‖ := fun j => hi j (Finset.mem_univ _)
  have hwi : w i ≠ 0 := by
    intro hwi
    obtain ⟨j,hj⟩ := hnonzero
    have hz : ‖w j‖ ≤ 0 := by simpa [hwi] using hmax j
    exact hj (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))
  let z : Fin 4 → ℤ_[p] := fun j => ⟨w j/w i, by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hwi)]
    exact hmax j⟩
  refine ⟨z,⟨i,Subtype.ext (div_self hwi)⟩,?_,?_⟩
  · apply Subtype.ext
    change (d.2.1 : ℚ_[p])*(w 1/w i)^2-(d.1 : ℚ_[p])*(w 0/w i)^2=
      (r2 : ℚ_[p])*(w 3/w i)^2
    field_simp
    linear_combination h1
  · apply Subtype.ext
    change (d.2.2 : ℚ_[p])*(w 2/w i)^2-(d.1 : ℚ_[p])*(w 0/w i)^2=
      (r3 : ℚ_[p])*(w 3/w i)^2
    field_simp
    linear_combination h2

theorem splitCover_primitive_int_residues {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p])
      (r2 : ℚ_[p]) (r3 : ℚ_[p])) :
    ∃ z : Fin 4 → ℤ, (∃ i, ¬(p : ℤ) ∣ z i) ∧
      (p : ℤ)^2 ∣ d.2.1*(z 1)^2-d.1*(z 0)^2-r2*(z 3)^2 ∧
      (p : ℤ)^2 ∣ d.2.2*(z 2)^2-d.1*(z 0)^2-r3*(z 3)^2 := by
  have hp2 : 1 < p^2 := by have hp := (Fact.out : p.Prime).two_le; nlinarith
  let : Fact (1 < p^2) := ⟨hp2⟩
  obtain ⟨w,⟨i,hi⟩,h1,h2⟩ := splitCover_integral_normalization_general d r2 r3 h
  let q : Fin 4 → ZMod (p^2) := fun j => PadicInt.toZModPow 2 (w j)
  let z : Fin 4 → ℤ := fun j => ((q j).val : ℤ)
  have hz (j : Fin 4) : (z j : ZMod (p^2)) = q j := by simp only [z,Int.cast_natCast,ZMod.natCast_zmod_val]
  have hqi : q i = 1 := by simp only [q,hi,map_one]
  refine ⟨z,⟨i,?_⟩,?_,?_⟩
  · have hzi : z i = 1 := by
      simp only [z,hqi,ZMod.val_one (p^2),Int.natCast_one]
    rw [hzi]
    exact (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))).not_dvd_one
  · have he : ((d.2.1*(z 1)^2-d.1*(z 0)^2-r2*(z 3)^2 : ℤ) : ZMod (p^2))=0 := by
      push_cast
      simp only [hz]
      have hm := congrArg (PadicInt.toZModPow 2) h1
      simp only [map_sub,map_mul,map_pow,map_intCast] at hm
      exact sub_eq_zero.mpr hm
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  · have he : ((d.2.2*(z 2)^2-d.1*(z 0)^2-r3*(z 3)^2 : ℤ) : ZMod (p^2))=0 := by
      push_cast
      simp only [hz]
      have hm := congrArg (PadicInt.toZModPow 2) h2
      simp only [map_sub,map_mul,map_pow,map_intCast] at hm
      exact sub_eq_zero.mpr hm
    simpa only [Nat.cast_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he

theorem splitCover_prime_support_first {p : ℕ} [Fact p.Prime]
    (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (h : SplitCoverSoluble (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p])
      (r2 : ℚ_[p]) (r3 : ℚ_[p])) (h1 : (p : ℤ) ∣ d.1) : (p : ℤ) ∣ r2*r3 := by
  by_contra hn
  have hr2 : ¬(p : ℤ) ∣ r2 := fun hdiv => hn (dvd_mul_of_dvd_left hdiv _)
  have hr3 : ¬(p : ℤ) ∣ r3 := fun hdiv => hn (dvd_mul_of_dvd_right hdiv _)
  have hp : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))
  obtain ⟨z,⟨i,hi⟩,he1,he2⟩ := splitCover_primitive_int_residues d r2 r3 h
  rcases squarefree_product_prime_parity d.1 d.2.1 d.2.2 hs1 hs2 hs3 hsq h1 with
    ⟨h2,h3⟩ | ⟨h2,h3⟩
  · obtain ⟨ha,hb,hc,ht⟩ := splitCover_two_divisors_force_nonprimitive
      p d.1 d.2.1 d.2.2 r2 r3 (z 0) (z 1) (z 2) (z 3) hp hs1 hs2 h1 h2 h3 hr2 hr3 he1 he2
    fin_cases i <;> contradiction
  · obtain ⟨ha,hc,hb,ht⟩ := splitCover_two_divisors_force_nonprimitive
      p d.1 d.2.2 d.2.1 r3 r2 (z 0) (z 2) (z 1) (z 3) hp hs1 hs3 h1 h3 h2 hr3 hr2 he2 he1
    fin_cases i <;> contradiction

theorem squarefree_int_dvd_of_prime_dvd (d N : ℤ) (hs : Squarefree d)
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → (p : ℤ) ∣ N) : d ∣ N := by
  by_cases hN : N = 0
  · rw [hN]; exact dvd_zero d
  rw [←Int.natAbs_dvd_natAbs]
  have hsd : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hs
  rw [←Nat.prod_primeFactors_of_squarefree hsd]
  apply (Nat.prod_primeFactors_dvd_iff (Int.natAbs_ne_zero.mpr hN)).mpr
  intro p hp
  obtain ⟨hprime,hdiv,_⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hprime,
    Int.natCast_dvd.mp (h p hprime (Int.natCast_dvd.mpr hdiv)),Int.natAbs_ne_zero.mpr hN⟩

theorem splitCover_support_first (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (h : SplitCoverEverywhereLocallySoluble d r2 r3) : d.1 ∣ r2*r3 := by
  apply squarefree_int_dvd_of_prime_dvd d.1 (r2*r3) hs1
  intro p hp hdiv
  let : Fact p.Prime := ⟨hp⟩
  exact splitCover_prime_support_first d r2 r3 hs1 hs2 hs3 hsq (h.2 p) hdiv

theorem splitCover_swap_first_second {K : Type*} [Field K]
    (d1 d2 d3 r2 r3 : K) (h : SplitCoverSoluble d1 d2 d3 r2 r3) :
    SplitCoverSoluble d2 d1 d3 (-r2) (r3-r2) := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := h
  let w : Fin 4 → K := ![z 1,z 0,z 2,z 3]
  refine ⟨w,?_,?_,?_⟩
  · fin_cases i
    · exact ⟨1,hi⟩
    · exact ⟨0,hi⟩
    · exact ⟨2,hi⟩
    · exact ⟨3,hi⟩
  · change d1*(z 0)^2-d2*(z 1)^2=(-r2)*(z 3)^2
    linear_combination -h1
  · change d3*(z 2)^2-d2*(z 1)^2=(r3-r2)*(z 3)^2
    linear_combination h2-h1

theorem splitCover_rotate_first_third {K : Type*} [Field K]
    (d1 d2 d3 r2 r3 : K) (h : SplitCoverSoluble d1 d2 d3 r2 r3) :
    SplitCoverSoluble d3 d1 d2 (-r3) (r2-r3) := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := h
  let w : Fin 4 → K := ![z 2,z 0,z 1,z 3]
  refine ⟨w,?_,?_,?_⟩
  · fin_cases i
    · exact ⟨1,hi⟩
    · exact ⟨2,hi⟩
    · exact ⟨0,hi⟩
    · exact ⟨3,hi⟩
  · change d1*(z 0)^2-d3*(z 2)^2=(-r3)*(z 3)^2
    linear_combination -h2
  · change d2*(z 1)^2-d3*(z 2)^2=(r2-r3)*(z 3)^2
    linear_combination h1-h2

theorem SplitCoverEverywhereLocallySoluble.swap_first_second
    (d : ECFullTriple) (r2 r3 : ℤ) (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    SplitCoverEverywhereLocallySoluble (d.2.1,d.1,d.2.2) (-r2) (r3-r2) := by
  constructor
  · simpa only [Int.cast_neg,Int.cast_sub] using
      splitCover_swap_first_second (d.1 : ℝ) (d.2.1 : ℝ) (d.2.2 : ℝ) r2 r3 h.1
  · intro p hp
    simpa only [Int.cast_neg,Int.cast_sub] using
      splitCover_swap_first_second (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p]) r2 r3 (h.2 p)

theorem SplitCoverEverywhereLocallySoluble.rotate_first_third
    (d : ECFullTriple) (r2 r3 : ℤ) (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    SplitCoverEverywhereLocallySoluble (d.2.2,d.1,d.2.1) (-r3) (r2-r3) := by
  constructor
  · simpa only [Int.cast_neg,Int.cast_sub] using
      splitCover_rotate_first_third (d.1 : ℝ) (d.2.1 : ℝ) (d.2.2 : ℝ) r2 r3 h.1
  · intro p hp
    simpa only [Int.cast_neg,Int.cast_sub] using
      splitCover_rotate_first_third (d.1 : ℚ_[p]) (d.2.1 : ℚ_[p]) (d.2.2 : ℚ_[p]) r2 r3 (h.2 p)

theorem splitCover_support_all (d : ECFullTriple) (r2 r3 : ℤ)
    (hs1 : Squarefree d.1) (hs2 : Squarefree d.2.1) (hs3 : Squarefree d.2.2)
    (hsq : IsSquare (d.1*d.2.1*d.2.2))
    (h : SplitCoverEverywhereLocallySoluble d r2 r3) :
    d.1 ∣ r2*r3 ∧ d.2.1 ∣ r2*(r2-r3) ∧ d.2.2 ∣ r3*(r2-r3) := by
  refine ⟨splitCover_support_first d r2 r3 hs1 hs2 hs3 hsq h,?_,?_⟩
  · have hsq' : IsSquare (d.2.1*d.1*d.2.2) := by convert hsq using 1; ring
    have hd := splitCover_support_first (d.2.1,d.1,d.2.2) (-r2) (r3-r2)
      hs2 hs1 hs3 hsq' (SplitCoverEverywhereLocallySoluble.swap_first_second d r2 r3 h)
    convert hd using 1; ring
  · have hsq' : IsSquare (d.2.2*d.1*d.2.1) := by convert hsq using 1; ring
    have hd := splitCover_support_first (d.2.2,d.1,d.2.1) (-r3) (r2-r3)
      hs3 hs1 hs2 hsq' (SplitCoverEverywhereLocallySoluble.rotate_first_third d r2 r3 h)
    apply dvd_neg.mp
    convert hd using 1; ring

end Z2Z4Rank6
