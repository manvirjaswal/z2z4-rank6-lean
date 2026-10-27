module

public import Z2Z4Rank6.BaseCurve

@[expose] public section

/-!
# The sixteen rational points above singular parameters

The rational-coordinate check in Theorem 1.2(c) of M. Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6

def singularParameter (m : ℚ) : Prop :=
  m ∈ ({0, 1, -1, 9, -9, 11, -11, 99, -99} : Finset ℚ)

/-- The two displayed sign families, read with all signs independent. -/
def exceptionalCPoint (c : CPoint) : Prop :=
  ((c.m = 1 ∨ c.m = -1) ∧ (c.u = 35 ∨ c.u = -35) ∧ (c.v = 35 ∨ c.v = -35)) ∨
  ((c.m = 99 ∨ c.m = -99) ∧ (c.u = 385 ∨ c.u = -385) ∧
    (c.v = 315 ∨ c.v = -315))

theorem CPoint.m_ne_zero (c : CPoint) : c.m ≠ 0 := by
  intro hm
  have hsq : IsSquare (1210 : ℚ) := ⟨c.u, by nlinarith [c.u_sq]⟩
  norm_num at hsq

theorem CPoint.m_ne_nine (c : CPoint) : c.m ≠ 9 := by
  intro hm
  have hsq : IsSquare (2425 : ℚ) := ⟨c.u, by nlinarith [c.u_sq]⟩
  norm_num at hsq

theorem CPoint.m_ne_neg_nine (c : CPoint) : c.m ≠ -9 := by
  intro hm
  have hsq : IsSquare (2425 : ℚ) := ⟨c.u, by nlinarith [c.u_sq]⟩
  norm_num at hsq

theorem CPoint.m_ne_eleven (c : CPoint) : c.m ≠ 11 := by
  intro hm
  have hsq : IsSquare (2425 : ℚ) := ⟨c.v, by nlinarith [c.v_sq]⟩
  norm_num at hsq

theorem CPoint.m_ne_neg_eleven (c : CPoint) : c.m ≠ -11 := by
  intro hm
  have hsq : IsSquare (2425 : ℚ) := ⟨c.v, by nlinarith [c.v_sq]⟩
  norm_num at hsq

theorem CPoint.coords_of_m_one (c : CPoint) (hm : c.m = 1 ∨ c.m = -1) :
    (c.u = 35 ∨ c.u = -35) ∧ (c.v = 35 ∨ c.v = -35) := by
  have hm2 : c.m^2 = 1 := by rcases hm with hm | hm <;> rw [hm] <;> norm_num
  constructor <;> apply sq_eq_sq_iff_eq_or_eq_neg.mp
  · nlinarith [c.u_sq]
  · nlinarith [c.v_sq]

theorem CPoint.coords_of_m_ninetynine (c : CPoint) (hm : c.m = 99 ∨ c.m = -99) :
    (c.u = 385 ∨ c.u = -385) ∧ (c.v = 315 ∨ c.v = -315) := by
  have hm2 : c.m^2 = 9801 := by rcases hm with hm | hm <;> rw [hm] <;> norm_num
  constructor <;> apply sq_eq_sq_iff_eq_or_eq_neg.mp
  · nlinarith [c.u_sq]
  · nlinarith [c.v_sq]

theorem singularParameter_iff_exceptional (c : CPoint) :
    singularParameter c.m ↔ exceptionalCPoint c := by
  constructor
  · intro hm
    simp only [singularParameter, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm
    · exact (c.m_ne_zero hm).elim
    · exact Or.inl ⟨Or.inl hm, c.coords_of_m_one (Or.inl hm)⟩
    · exact Or.inl ⟨Or.inr hm, c.coords_of_m_one (Or.inr hm)⟩
    · exact (c.m_ne_nine hm).elim
    · exact (c.m_ne_neg_nine hm).elim
    · exact (c.m_ne_eleven hm).elim
    · exact (c.m_ne_neg_eleven hm).elim
    · exact Or.inr ⟨Or.inl hm, c.coords_of_m_ninetynine (Or.inl hm)⟩
    · exact Or.inr ⟨Or.inr hm, c.coords_of_m_ninetynine (Or.inr hm)⟩
  · rintro (⟨hm,_,_⟩ | ⟨hm,_,_⟩) <;> rcases hm with hm | hm <;>
      simp [singularParameter, hm]

def singularCPoint (i : Fin 4) (j k : Fin 2) : CPoint where
  m := ![1,-1,99,-99] i
  u := if j = 0 then (if i < 2 then 35 else 385) else -(if i < 2 then 35 else 385)
  v := if k = 0 then (if i < 2 then 35 else 315) else -(if i < 2 then 35 else 315)
  u_sq := by fin_cases i <;> fin_cases j <;> norm_num
  v_sq := by fin_cases i <;> fin_cases k <;> norm_num

theorem singularCPoint_injective :
    Function.Injective (fun t : Fin 4 × Fin 2 × Fin 2 => singularCPoint t.1 t.2.1 t.2.2) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
  have hm := congrArg CPoint.m h
  have hu := congrArg CPoint.u h
  have hv := congrArg CPoint.v h
  have hi : i = i' := by
    fin_cases i <;> fin_cases i' <;> first | rfl | norm_num [singularCPoint] at hm
  subst i'
  have hj : j = j' := by
    fin_cases i <;> fin_cases j <;> fin_cases j' <;> first | rfl | norm_num [singularCPoint] at hu
  subst j'
  have hk : k = k' := by
    fin_cases i <;> fin_cases k <;> fin_cases k' <;> first | rfl | norm_num [singularCPoint] at hv
  subst k'
  rfl

noncomputable def singularCPoints : Finset CPoint := by
  classical
  exact Finset.univ.image (fun t : Fin 4 × Fin 2 × Fin 2 => singularCPoint t.1 t.2.1 t.2.2)

theorem singularCPoints_card : singularCPoints.card = 16 := by
  classical
  rw [singularCPoints, Finset.card_image_of_injective _ singularCPoint_injective]
  norm_num

theorem mem_singularCPoints_iff (c : CPoint) : c ∈ singularCPoints ↔ exceptionalCPoint c := by
  classical
  constructor
  · intro hc
    obtain ⟨⟨i,j,k⟩, _, rfl⟩ := Finset.mem_image.mp hc
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [singularCPoint, exceptionalCPoint]
  · rintro (⟨hm,hu,hv⟩ | ⟨hm,hu,hv⟩)
    all_goals
      rcases hm with hm | hm <;> rcases hu with hu | hu <;> rcases hv with hv | hv
    all_goals
      apply Finset.mem_image.mpr
    all_goals
      refine ⟨(if c.m = 1 then 0 else if c.m = -1 then 1 else if c.m = 99 then 2 else 3,
        if c.u = 35 ∨ c.u = 385 then 0 else 1,
        if c.v = 35 ∨ c.v = 315 then 0 else 1), Finset.mem_univ _, ?_⟩
      ext <;> norm_num [singularCPoint, hm, hu, hv]

end Z2Z4Rank6
