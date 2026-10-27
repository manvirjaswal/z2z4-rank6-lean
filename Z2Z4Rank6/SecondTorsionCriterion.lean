module

public import Z2Z4Rank6.SecondFamily
public import Z2Z4Rank6.Torsion

@[expose] public section

/-! The second family splits as E(a,b); the proved nonsquare criterion
gives ellipticity and exact rational torsion. Source: Jaswal, Theorem 8.1(c). -/
namespace Z2Z4Rank6.SecondTorsionCofinite
open SecondFamily
noncomputable section

def splitA (P : G2Point ℚ) : ℚ := (P.s1-1)*(P.s1-lambda)
def splitB (P : G2Point ℚ) : ℚ := (P.s1+1)*(P.s1+lambda)

theorem F_split_G2 (P : G2Point ℚ) : F P.W=E (splitA P) (splitB P) := by
  rw [←P.s1_sq]
  exact F_split P.s1

theorem split_product (P : G2Point ℚ) : splitA P*splitB P= -V P.W := by
  rw [←P.s1_sq]
  dsimp [splitA,splitB,V]
  ring

/-- Smoothness and the exact rational torsion group follow from the
proved nonsquare criterion whenever both signed V-values are nonsquares. -/
theorem good_torsion_exact_of_nonsquares (hMazur : MazurTorsionTheorem)
    (P : G2Point ℚ) (hp : ¬IsSquare (V P.W)) (hn : ¬IsSquare (-V P.W)) :
    GoodCurve (F P.W) ∧ TorsionExact (F P.W) := by
  have hgood : (F P.W).IsElliptic := by
    apply P.rational_elliptic_iff.mpr
    constructor
    · intro hw
      apply hp
      simp [V,hw]
    · intro hw
      apply hp
      simp [V,hw]
  have hprod : splitA P*splitB P*((splitA P)^2-(splitB P)^2)≠0 := by
    intro hz
    apply hgood.isUnit.ne_zero
    rw [F_split_G2,E_discriminant,
      show 16*(splitA P)^4*(splitB P)^4*((splitA P)^2-(splitB P)^2)^2=
        16*(splitA P*splitB P*((splitA P)^2-(splitB P)^2))^2*(splitA P)^2*(splitB P)^2 by ring,
      hz]
    ring
  refine ⟨hgood,?_⟩
  rw [F_split_G2]
  apply E_torsion_exact hMazur _ _ hprod
  · rw [split_product]
    exact hn
  · rw [split_product,neg_neg]
    exact hp

end
end Z2Z4Rank6.SecondTorsionCofinite
