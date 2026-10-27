module

public import Z2Z4Rank6.SecondReductionRank
public import Z2Z4Rank6.IntegralResidue

@[expose] public section

/-!
# Congruence regularity for the second family's sections

The six primes and signed sections are those of Theorem 8.1(d). Coordinate
congruence is imposed on the four affine G₂ coordinates. All section
denominators are checked units in these residue classes.
-/
namespace Z2Z4Rank6
open SecondFamily

/-- All four coordinates are integral and reduce to the printed base
point at the indicated prime. -/
def SecondCongruentAt (i:Fin 6) (P:G2Point ℚ) : Prop :=
  IntegralAt (SecondReductionData.primes i) P.W ∧
  IntegralAt (SecondReductionData.primes i) P.s1 ∧
  IntegralAt (SecondReductionData.primes i) P.s2 ∧
  IntegralAt (SecondReductionData.primes i) P.s3 ∧
  residue (SecondReductionData.primes i) P.W=residue (SecondReductionData.primes i) SecondReductionData.basePoint.W ∧
  residue (SecondReductionData.primes i) P.s1=residue (SecondReductionData.primes i) SecondReductionData.basePoint.s1 ∧
  residue (SecondReductionData.primes i) P.s2=residue (SecondReductionData.primes i) SecondReductionData.basePoint.s2 ∧
  residue (SecondReductionData.primes i) P.s3=residue (SecondReductionData.primes i) SecondReductionData.basePoint.s3

def SecondCongruenceSet : Set (G2Point ℚ) := {P | ∀i:Fin 6,SecondCongruentAt i P}

theorem second_base_coordinates_integral (i:Fin 6) :
    IntegralAt (SecondReductionData.primes i) SecondReductionData.basePoint.W ∧
    IntegralAt (SecondReductionData.primes i) SecondReductionData.basePoint.s1 ∧
    IntegralAt (SecondReductionData.primes i) SecondReductionData.basePoint.s2 ∧
    IntegralAt (SecondReductionData.primes i) SecondReductionData.basePoint.s3 := by
  unfold IntegralAt
  fin_cases i <;> decide +kernel

theorem second_base_congruent (i:Fin 6) : SecondCongruentAt i SecondReductionData.basePoint := by
  have h:=second_base_coordinates_integral i
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,rfl,rfl,rfl,rfl⟩

/-- Equality after reduction, together with the two required integral domains. -/
def ResidueCongruent (p:ℕ) [Fact p.Prime] (a b:ℚ) : Prop :=
  IntegralAt p a ∧ IntegralAt p b ∧ residue p a=residue p b

namespace ResidueCongruent
variable {p:ℕ} [Fact p.Prime] {a a₀ b b₀:ℚ}
theorem refl (h:IntegralAt p a) : ResidueCongruent p a a := ⟨h,h,rfl⟩
theorem add (ha:ResidueCongruent p a a₀) (hb:ResidueCongruent p b b₀) :
    ResidueCongruent p (a+b) (a₀+b₀) := by
  exact ⟨ha.1.add hb.1,ha.2.1.add hb.2.1,by rw [residue_add ha.1 hb.1,residue_add ha.2.1 hb.2.1,ha.2.2,hb.2.2]⟩
theorem mul (ha:ResidueCongruent p a a₀) (hb:ResidueCongruent p b b₀) :
    ResidueCongruent p (a*b) (a₀*b₀) := by
  exact ⟨ha.1.mul hb.1,ha.2.1.mul hb.2.1,by rw [residue_mul ha.1 hb.1,residue_mul ha.2.1 hb.2.1,ha.2.2,hb.2.2]⟩
theorem neg (ha:ResidueCongruent p a a₀) : ResidueCongruent p (-a) (-a₀) :=
  ⟨ha.1.neg,ha.2.1.neg,by rw [residue_neg,residue_neg,ha.2.2]⟩
theorem sub (ha:ResidueCongruent p a a₀) (hb:ResidueCongruent p b b₀) :
    ResidueCongruent p (a-b) (a₀-b₀) := by simpa only [sub_eq_add_neg] using ha.add hb.neg
theorem pow (ha:ResidueCongruent p a a₀) (n:ℕ) : ResidueCongruent p (a^n) (a₀^n) :=
  ⟨ha.1.pow n,ha.2.1.pow n,by rw [residue_pow ha.1,residue_pow ha.2.1,ha.2.2]⟩
theorem inv (ha:ResidueCongruent p a a₀) (hu:residue p a₀≠0) :
    ResidueCongruent p a⁻¹ a₀⁻¹ := by
  have hu' : residue p a≠0 := by rwa [ha.2.2]
  exact ⟨ha.1.inv hu',ha.2.1.inv hu,by rw [residue_inv ha.1 hu',residue_inv ha.2.1 hu,ha.2.2]⟩
theorem div (ha:ResidueCongruent p a a₀) (hb:ResidueCongruent p b b₀)
    (hu:residue p b₀≠0) : ResidueCongruent p (a/b) (a₀/b₀) := by
  simpa only [div_eq_mul_inv] using ha.mul (hb.inv hu)
end ResidueCongruent

theorem second_coordinate_congruences (i:Fin 6) (P:G2Point ℚ) (h:SecondCongruentAt i P) :
    ResidueCongruent (SecondReductionData.primes i) P.W SecondReductionData.basePoint.W ∧
    ResidueCongruent (SecondReductionData.primes i) P.s1 SecondReductionData.basePoint.s1 ∧
    ResidueCongruent (SecondReductionData.primes i) P.s2 SecondReductionData.basePoint.s2 ∧
    ResidueCongruent (SecondReductionData.primes i) P.s3 SecondReductionData.basePoint.s3 := by
  have hb:=second_base_coordinates_integral i
  exact ⟨⟨h.1,hb.1,h.2.2.2.2.1⟩,⟨h.2.1,hb.2.1,h.2.2.2.2.2.1⟩,
    ⟨h.2.2.1,hb.2.2.1,h.2.2.2.2.2.2.1⟩,⟨h.2.2.2.1,hb.2.2.2,h.2.2.2.2.2.2.2⟩⟩

syntax "second_residue_arith" term : tactic
macro_rules
  | `(tactic| second_residue_arith $idx:term) => `(tactic|
      first
      | assumption
      | exact ResidueCongruent.refl (by unfold IntegralAt; fin_cases $idx:term <;> decide +kernel)
      | apply ResidueCongruent.pow; second_residue_arith $idx
      | apply ResidueCongruent.add <;> second_residue_arith $idx
      | apply ResidueCongruent.sub <;> second_residue_arith $idx
      | apply ResidueCongruent.mul <;> second_residue_arith $idx
      | apply ResidueCongruent.neg; second_residue_arith $idx
      | apply ResidueCongruent.div
        · second_residue_arith $idx
        · second_residue_arith $idx
        · fin_cases $idx:term <;> decide +kernel
      | apply ResidueCongruent.inv
        · second_residue_arith $idx
        · fin_cases $idx:term <;> decide +kernel)

theorem second_section_congruences (i:Fin 6) (P:G2Point ℚ)
    (h:SecondCongruentAt i P) (j:Fin 6) :
    ResidueCongruent (SecondReductionData.primes i) (P.sixX j) (SecondReductionData.basePoint.sixX j) ∧
    ResidueCongruent (SecondReductionData.primes i) (P.sixY j) (SecondReductionData.basePoint.sixY j) := by
  obtain ⟨hW,hs1,hs2,hs3⟩:=second_coordinate_congruences i P h
  constructor
  · fin_cases j <;>
      dsimp only [G2Point.sixX,G2Point.untwistedX2,G2Point.untwistedX3,
        G2Point.untwistedX4,G2Point.untwistedX5,G2Point.untwistedX6,
        x1,x2,x3,x4,x5,x6,qA,qB,qH,sigma,iotaScale] <;>
      simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> second_residue_arith i
  · fin_cases j <;>
      dsimp only [G2Point.sixY,G2Point.untwistedY2,G2Point.untwistedY3,
        G2Point.untwistedY4,G2Point.untwistedY5,G2Point.untwistedY6,
        y1,y2,y3,y4,y5,y6,f2,f6,qA,qB,qH,sigma,iotaScale] <;>
      simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> second_residue_arith i


end Z2Z4Rank6
