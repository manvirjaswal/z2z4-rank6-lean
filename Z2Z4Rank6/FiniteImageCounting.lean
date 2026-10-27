module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Z2Z4Rank6.JDegree
public import Z2Z4Rank6.SecondJDegree

@[expose] public section

/-!
# Finite image counting with bounded fibers

A finite set with fibers of size at most n has cardinality at most n times
its image cardinality. Applied to the smooth-point j maps, the proved
fiber bounds give factors 192and96 for the two families in Jaswal,
DOI 10.5281/zenodo.23437117, Remark 6.3 and Theorem 8.1(c).
-/
namespace Z2Z4Rank6.FiniteImageCounting

/-- Count a finite domain by its fibers inside that domain. -/
theorem ncard_le_mul_ncard_image {α β : Type*} (S : Set α) (hS : S.Finite)
    (f : α→β) (n : ℕ)
    (hfibers : ∀b∈f '' S,{a∈S | f a=b}.ncard≤n) :
    S.ncard≤n*(f '' S).ncard := by
  classical
  have h := Finset.card_le_mul_card_image (f:=f) hS.toFinset n (by
    intro b hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
    have hbS : b∈f '' S := ⟨a,by simpa using ha,hab⟩
    have hset : ((hS.toFinset.filter (fun a => f a=b) : Finset α) : Set α)=
        {a∈S | f a=b} := by
      ext a
      simp
    have hcard := congrArg Set.ncard hset
    simp only [Set.ncard_coe_finset] at hcard
    rw [hcard]
    exact hfibers b hbS)
  have hsCard : hS.toFinset.card=S.ncard := (Set.ncard_eq_toFinset_card S hS).symm
  have hiCard : (hS.toFinset.image f).card=(f '' S).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (hS.image f),
      Set.Finite.toFinset_image f hS (hS.image f)]
  simpa only [hsCard,hiCard] using h

/-- An image of a finite set has at most as many elements as the set. -/
theorem ncard_image_le {α β : Type*} (S : Set α) (hS : S.Finite) (f : α→β) :
    (f '' S).ncard≤S.ncard := Set.ncard_image_le hS

/-- The two elementary finite-image inequalities. -/
theorem ncard_image_bounds {α β : Type*} (S : Set α) (hS : S.Finite)
    (f : α→β) (n : ℕ) (hfibers : ∀b∈f '' S,{a∈S | f a=b}.ncard≤n) :
    (f '' S).ncard≤S.ncard ∧ S.ncard≤n*(f '' S).ncard :=
  ⟨ncard_image_le S hS f,ncard_le_mul_ncard_image S hS f n hfibers⟩

end Z2Z4Rank6.FiniteImageCounting

namespace Z2Z4Rank6

/-- Any finite set of smooth first-family points has at most 192 times as
many points as distinct j-values. -/
theorem ncard_CPoint_le_192_mul_jimage (S : Set CPoint) (hS : S.Finite)
    (hSmooth : ∀c∈S,GoodCurve (X c.m)) :
    S.ncard≤192*((fun c : CPoint => jValue (X c.m)) '' S).ncard := by
  apply FiniteImageCounting.ncard_le_mul_ncard_image S hS _ 192
  intro j _
  exact (Set.ncard_le_ncard
    (fun c hc => ⟨hSmooth c hc.1,hc.2⟩ :
      {c∈S | jValue (X c.m)=j}⊆{c : CPoint | GoodCurve (X c.m) ∧ jValue (X c.m)=j})
    (finite_j_CPoint_fiber j)).trans (ncard_j_CPoint_fiber_le j)

namespace SecondFamily

/-- Any finite set of smooth second-family points has at most 96 times as
many points as distinct j-values. -/
theorem ncard_G2Point_le_96_mul_jimage (S : Set (G2Point ℚ)) (hS : S.Finite)
    (hSmooth : ∀P∈S,GoodCurve (F P.W)) :
    S.ncard≤96*((fun P : G2Point ℚ => jValue (F P.W)) '' S).ncard := by
  apply FiniteImageCounting.ncard_le_mul_ncard_image S hS _ 96
  intro j _
  exact (Set.ncard_le_ncard
    (fun P hP => ⟨hSmooth P hP.1,hP.2⟩ :
      {P∈S | jValue (F P.W)=j}⊆{P : G2Point ℚ | GoodCurve (F P.W) ∧ jValue (F P.W)=j})
    (finite_j_G2Point_fiber j)).trans (ncard_j_G2Point_fiber_le j)

end SecondFamily
end Z2Z4Rank6
