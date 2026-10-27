import Z2Z4Rank6.ECFullSelmerModel
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic

/-!
# Canonical squarefree representatives of rational covering coordinates

Elementary square extraction in Z, followed by rational homogeneous scaling.
-/
namespace Z2Z4Rank6

theorem rat_exists_squarefree_factor (q : ℚ) (hq : q ≠ 0) :
    ∃ (d : ℤ) (s : ℚ), Squarefree d ∧ s ≠ 0 ∧ q = (d : ℚ)*s^2 := by
  obtain ⟨e,d,he,hd⟩ := exists_sq_mul_squarefree (q.num*(q.den : ℤ))
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have he0 : e ≠ 0 := by
    intro he0
    rw [he0,zero_pow (by decide),zero_mul] at he
    exact mul_ne_zero hn (by exact_mod_cast q.den_ne_zero) he.symm
  refine ⟨d,(e : ℚ)/(q.den : ℚ),hd,div_ne_zero (by exact_mod_cast he0) hden,?_⟩
  have hc : (e : ℚ)^2*(d : ℚ)=(q.num : ℚ)*(q.den : ℚ) := by exact_mod_cast he
  conv_lhs => rw [←Rat.num_div_den q]
  field_simp
  linear_combination -hc

theorem splitCoverSoluble_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (d1 d2 d3 r2 r3 : K)
    (h : SplitCoverSoluble d1 d2 d3 r2 r3) :
    SplitCoverSoluble (f d1) (f d2) (f d3) (f r2) (f r3) := by
  obtain ⟨z,⟨i,hi⟩,h1,h2⟩ := h
  refine ⟨fun j => f (z j),⟨i,by simpa only [map_ne_zero] using hi⟩,?_,?_⟩
  · have hm := congrArg f h1
    simpa only [map_sub,map_mul,map_pow] using hm
  · have hm := congrArg f h2
    simpa only [map_sub,map_mul,map_pow] using hm

theorem splitCover_global_implies_everywhere (d : ECFullTriple) (r2 r3 : ℤ)
    (h : SplitCoverSoluble (d.1 : ℚ) (d.2.1 : ℚ) (d.2.2 : ℚ) (r2 : ℚ) (r3 : ℚ)) :
    SplitCoverEverywhereLocallySoluble d r2 r3 := by
  constructor
  · simpa only [map_intCast] using splitCoverSoluble_map (Rat.castHom ℝ)
      (d.1 : ℚ) (d.2.1 : ℚ) (d.2.2 : ℚ) (r2 : ℚ) (r3 : ℚ) h
  · intro p hp
    simpa only [map_intCast] using splitCoverSoluble_map (Rat.castHom ℚ_[p])
      (d.1 : ℚ) (d.2.1 : ℚ) (d.2.2 : ℚ) (r2 : ℚ) (r3 : ℚ) h

theorem canonicalize_splitCover (q1 q2 q3 r2 r3 : ℚ)
    (hq1 : q1≠0) (hq2 : q2≠0) (hq3 : q3≠0)
    (hsq : IsSquare (q1*q2*q3)) (h : SplitCoverSoluble q1 q2 q3 r2 r3) :
    ∃ d : ECFullTriple, Squarefree d.1 ∧ Squarefree d.2.1 ∧ Squarefree d.2.2 ∧
      IsSquare (d.1*d.2.1*d.2.2) ∧
      SplitCoverSoluble (d.1 : ℚ) (d.2.1 : ℚ) (d.2.2 : ℚ) r2 r3 ∧
      (squareClass q1,squareClass q2) = (squareClass (d.1 : ℚ),squareClass (d.2.1 : ℚ)) := by
  obtain ⟨d1,s1,hd1,hs1,h1⟩ := rat_exists_squarefree_factor q1 hq1
  obtain ⟨d2,s2,hd2,hs2,h2⟩ := rat_exists_squarefree_factor q2 hq2
  obtain ⟨d3,s3,hd3,hs3,h3⟩ := rat_exists_squarefree_factor q3 hq3
  refine ⟨(d1,d2,d3),hd1,hd2,hd3,?_,?_,?_⟩
  · apply Rat.isSquare_intCast_iff.mp
    obtain ⟨n,hn⟩ := hsq
    refine ⟨n/(s1*s2*s3),?_⟩
    push_cast
    field_simp
    rw [h1,h2,h3] at hn
    linear_combination hn
  · obtain ⟨z,⟨i,hi⟩,hz1,hz2⟩ := h
    let w : Fin 4 → ℚ := ![s1*z 0,s2*z 1,s3*z 2,z 3]
    refine ⟨w,⟨i,?_⟩,?_,?_⟩
    · fin_cases i <;> simpa [w,mul_ne_zero_iff,hs1,hs2,hs3] using hi
    · change (d2 : ℚ)*(s2*z 1)^2-(d1 : ℚ)*(s1*z 0)^2=r2*(z 3)^2
      rw [h1,h2] at hz1
      linear_combination hz1
    · change (d3 : ℚ)*(s3*z 2)^2-(d1 : ℚ)*(s1*z 0)^2=r3*(z 3)^2
      rw [h1,h3] at hz2
      linear_combination hz2
  · apply Prod.ext
    · exact squareClass_eq_of_factor q1 d1 s1 hq1 (by exact_mod_cast hd1.ne_zero) hs1 h1
    · exact squareClass_eq_of_factor q2 d2 s2 hq2 (by exact_mod_cast hd2.ne_zero) hs2 h2

end Z2Z4Rank6
