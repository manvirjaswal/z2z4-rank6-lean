import Z2Z4Rank6.BaseCurveArithmetic
import Z2Z4Rank6.Torsion
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Exact torsion on the printed curve E_C

The root translation `x ↦ x-404` identifies E_C with `E_{27,22}`. This permits
the torsion assertion of Lemma 4.1(b) in M. Jaswal, *Infinitely many elliptic
curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117, to use the proved nonsquare criterion of Lemma 6.1.
The additive equivalence below uses Mathlib's point groups.
-/

namespace Z2Z4Rank6

open WeierstrassCurve Affine Affine.Point

instance ecSplit_isElliptic : (E (27 : ℚ) 22).IsElliptic :=
  E_good 27 22 (by norm_num)

theorem ec_split_equation (x y : ℚ) :
    EC.toAffine.Equation x y ↔ (E (27 : ℚ) 22).toAffine.Equation (x-404) y := by
  rw [ec_equation_iff, E_equation_iff]
  ring_nf

def ecToSplit : RationalPoints EC → RationalPoints (E (27 : ℚ) 22)
  | .zero => 0
  | .some x y h => .mk ((ec_split_equation x y).mp h.1)

def splitToEC : RationalPoints (E (27 : ℚ) 22) → RationalPoints EC
  | .zero => 0
  | .some x y h => .mk ((ec_split_equation (x+404) y).mpr (by simpa using h.1))

theorem ecToSplit_left_inverse : Function.LeftInverse splitToEC ecToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [ecToSplit, splitToEC, Point.mk]

theorem ecToSplit_right_inverse : Function.RightInverse splitToEC ecToSplit := by
  intro P
  cases P with
  | zero => rfl
  | some x y h => simp [ecToSplit, splitToEC, Point.mk]

theorem ec_split_slope (x1 x2 y1 y2 : ℚ) :
    (E (27 : ℚ) 22).toAffine.slope (x1-404) (x2-404) y1 y2 =
      EC.toAffine.slope x1 x2 y1 y2 := by
  simp only [slope, negY, E, EC, zero_mul, sub_zero, sub_left_inj]
  split_ifs <;> ring

theorem ec_split_addX (x1 x2 l : ℚ) :
    (E (27 : ℚ) 22).toAffine.addX (x1-404) (x2-404) l =
      EC.toAffine.addX x1 x2 l - 404 := by
  unfold addX
  simp only [E, EC]
  ring

theorem ec_split_addY (x1 x2 y1 l : ℚ) :
    (E (27 : ℚ) 22).toAffine.addY (x1-404) (x2-404) y1 l =
      EC.toAffine.addY x1 x2 y1 l := by
  unfold addY negAddY addX negY
  simp only [E, EC]
  ring

theorem ecToSplit_add (P Q : RationalPoints EC) :
    ecToSplit (P+Q) = ecToSplit P + ecToSplit Q := by
  cases P with
  | zero => rfl
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      change ecToSplit ((Point.some x1 y1 h1) + 0) = ecToSplit (.some x1 y1 h1) + 0
      rw [add_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hv : x1 = x2 ∧ y1 = -y2
      · rw [Point.add_of_Y_eq hv.1 (by simpa [EC, negY] using hv.2)]
        simp only [ecToSplit, Point.mk]
        exact (Point.add_of_Y_eq (by rw [hv.1]) (by simpa [E, negY] using hv.2)).symm
      · rw [Point.add_some (by simpa [EC, negY] using hv)]
        simp only [ecToSplit, Point.mk]
        rw [Point.add_some (by simpa [E, negY, sub_left_inj] using hv)]
        congr 1
        · rw [ec_split_slope, ec_split_addX]
        · rw [ec_split_slope, ec_split_addY]

def ecSplitEquiv : RationalPoints EC ≃+ RationalPoints (E (27 : ℚ) 22) where
  toFun := ecToSplit
  invFun := splitToEC
  left_inv := ecToSplit_left_inverse
  right_inv := ecToSplit_right_inverse
  map_add' := ecToSplit_add

theorem ec_torsion_exact (hMazur : MazurTorsionTheorem) : TorsionExact EC := by
  obtain ⟨e⟩ := E_torsion_exact hMazur 27 22 (by norm_num) (by norm_num) (by norm_num)
  exact ⟨((ecSplitEquiv.addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr ecSplitEquiv.map_torsion)).trans e⟩

/-- The printed generator of order four on E_C. -/
def ecFourGenerator : RationalPoints EC :=
  .mk ((ec_equation_iff (-190) 2970).mpr (by norm_num))

/-- The printed independent generator of order two on E_C. -/
def ecTwoGenerator : RationalPoints EC :=
  .mk ((ec_equation_iff (-80) 0).mpr (by norm_num))

def ecFourDouble : RationalPoints EC :=
  .mk ((ec_equation_iff 404 0).mpr (by norm_num))

theorem ecFourGenerator_double : 2 • ecFourGenerator = ecFourDouble := by
  norm_num [two_nsmul, ecFourGenerator, ecFourDouble, Point.mk, Point.add_def, Point.add,
    negY, slope, addX, addY, negAddY, EC]

theorem ecFourDouble_double : ecFourDouble + ecFourDouble = 0 := by
  apply Point.add_self_of_Y_eq
  norm_num [negY, EC]

theorem ecFourGenerator_four : 4 • ecFourGenerator = 0 := by
  calc
    4 • ecFourGenerator = 2 • ecFourGenerator + 2 • ecFourGenerator := by abel
    _ = 0 := by rw [ecFourGenerator_double]; exact ecFourDouble_double

theorem ecTwoGenerator_two : 2 • ecTwoGenerator = 0 := by
  rw [two_nsmul]
  apply Point.add_self_of_Y_eq
  norm_num [negY, EC]

theorem ecTwoGenerator_ne_zero : ecTwoGenerator ≠ 0 := Point.some_ne_zero _

theorem ecFourGenerator_two_ne_zero : 2 • ecFourGenerator ≠ 0 := by
  rw [ecFourGenerator_double]
  exact Point.some_ne_zero _

theorem ecGenerators_independent : ecTwoGenerator ≠ 2 • ecFourGenerator := by
  rw [ecFourGenerator_double]
  intro h
  have hx := (Point.some.inj h).1
  norm_num at hx

/-- The two coordinate points printed in Lemma 4.1(b) generate the
whole rational torsion subgroup, under Mazur's generic classification. -/
theorem ec_printed_generators (hMazur : MazurTorsionTheorem) :
    AddSubgroup.closure ({ecTwoGenerator,ecFourGenerator} : Set (RationalPoints EC)) =
      AddCommGroup.torsion (RationalPoints EC) := by
  classical
  let H := AddSubgroup.closure ({ecTwoGenerator,ecFourGenerator} : Set (RationalPoints EC))
  have hT : ecTwoGenerator ∈ H := AddSubgroup.subset_closure (by simp)
  have hQ : ecFourGenerator ∈ H := AddSubgroup.subset_closure (by simp)
  have hle : H ≤ AddCommGroup.torsion (RationalPoints EC) := by
    apply (AddSubgroup.closure_le _).mpr
    intro P hP
    rcases hP with hP | hP
    · rw [hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, ecTwoGenerator_two⟩
    · rw [Set.mem_singleton_iff.mp hP]
      exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨4, by norm_num, ecFourGenerator_four⟩
  let T : H := ⟨ecTwoGenerator,hT⟩
  let Q : H := ⟨ecFourGenerator,hQ⟩
  obtain ⟨f,hf⟩ := two_four_injective T Q
    (Subtype.ext ecTwoGenerator_two) (Subtype.ext ecFourGenerator_four)
    (fun h => ecTwoGenerator_ne_zero (congrArg Subtype.val h))
    (fun h => ecFourGenerator_two_ne_zero (congrArg Subtype.val h))
    (fun h => ecGenerators_independent (congrArg Subtype.val h))
  obtain ⟨e⟩ := ec_torsion_exact hMazur
  have : Finite (AddCommGroup.torsion (RationalPoints EC)) :=
    Finite.of_equiv (ZMod 2 × ZMod 4) e.symm.toEquiv
  have : Finite H := Finite.of_injective (AddSubgroup.inclusion hle)
    (AddSubgroup.inclusion_injective hle)
  have hcard : Nat.card (AddCommGroup.torsion (RationalPoints EC)) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  exact AddSubgroup.eq_of_le_of_card_ge hle (by
    rw [hcard]
    simpa [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf)

end Z2Z4Rank6
