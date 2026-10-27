module

public import Z2Z4Rank6.SecondReductionCheck
public import Common.Elliptic.FiniteAbelianCertificates

@[expose] public section

/-!
# The reduction groups at 59 and 67 in Theorem 8.1(d)

The finite-field point groups of E_{460019200,11180308689} at
59 and 67 are Z/36 × Z/2. The generators are respectively (5,25),(14,0)
and (2,19),(5,0). Each 72-residue kernel certificate is checked against
the group law, and the three-primary subgroups are cyclic.
-/
namespace Z2Z4Rank6.SecondReductionStructure
noncomputable section
open Common.WeierstrassCoordinates Common.FiniteAbelianCertificates

def index : Fin 2 → Fin 6 := ![2,3]
abbrev C (i : Fin 2) := SecondReductionData.curve (index i)
abbrev Group (i : Fin 2) := (C i).toAffine.Point

def generatorX : Fin 2 → ℕ := ![5,2]
def generatorY : Fin 2 → ℕ := ![25,19]
def torsionX : Fin 2 → ℕ := ![14,5]

def P (i : Fin 2) : Group i :=
  .mk (x:=(generatorX i : ZMod (SecondReductionData.primes (index i))))
    (y:=(generatorY i : ZMod (SecondReductionData.primes (index i)))) (by
      rw [WeierstrassCurve.Affine.equation_iff]
      fin_cases i <;> decide +kernel)

def T (i : Fin 2) : Group i :=
  .mk (x:=(torsionX i : ZMod (SecondReductionData.primes (index i)))) (y:=0) (by
    rw [WeierstrassCurve.Affine.equation_iff]
    fin_cases i <;> decide +kernel)

theorem P_mul (i : Fin 2) : 36 • P i=0 := by
  apply encode_injective (C i)
  rw [encode_nsmul]
  change coordinateMul (C i) 36
    (some ((generatorX i : ZMod (SecondReductionData.primes (index i))),
      (generatorY i : ZMod (SecondReductionData.primes (index i)))) )=none
  fin_cases i <;> decide +kernel

theorem T_mul (i : Fin 2) : 2 • T i=0 := by
  apply encode_injective (C i)
  rw [encode_nsmul]
  change coordinateMul (C i) 2
    (some ((torsionX i : ZMod (SecondReductionData.primes (index i))),0))=none
  fin_cases i <;> decide +kernel

theorem kernel_certificate (i : Fin 2) : ∀ a : Fin 36, ∀ b : Fin 2,
    coordinateAdd (C i)
      (coordinateMul (C i) a.val
        (some ((generatorX i : ZMod (SecondReductionData.primes (index i))),
          (generatorY i : ZMod (SecondReductionData.primes (index i))))))
      (coordinateMul (C i) b.val
        (some ((torsionX i : ZMod (SecondReductionData.primes (index i))),0)))=none →
      a.val=0 ∧ b.val=0 := by
  fin_cases i <;> decide +kernel

theorem kernel_zero (i : Fin 2) (a : Fin 36) (b : Fin 2)
    (h : a.val • P i+b.val • T i=0) : a.val=0 ∧ b.val=0 := by
  have hc := congrArg encode h
  rw [encode_add,encode_nsmul,encode_nsmul] at hc
  exact kernel_certificate i a b hc

theorem group_card (i : Fin 2) : Nat.card (Group i)=72 := by
  have hc := SecondReductionData.curve_card (index i)
  fin_cases i <;> exact hc

/-- Additive equivalences with the printed finite groups. -/
def groupEquiv (i : Fin 2) : Group i ≃+ (ZMod 36 × ZMod 2) :=
  (productEquiv 36 2 (P i) (T i) (P_mul i) (T_mul i) (kernel_zero i) (group_card i)).symm

theorem group_structure_at_59 :
    Nonempty ((SecondReductionData.curve 2).toAffine.Point ≃+ (ZMod 36 × ZMod 2)) :=
  ⟨groupEquiv 0⟩

theorem group_structure_at_67 :
    Nonempty ((SecondReductionData.curve 3).toAffine.Point ≃+ (ZMod 36 × ZMod 2)) :=
  ⟨groupEquiv 1⟩

theorem three_primary_cyclic (i : Fin 2) :
    IsAddCyclic (AddCommGroup.primaryComponent (Group i) 3) :=
  Common.FiniteAbelianCertificates.three_primary_cyclic (groupEquiv i)

/-- All six printed reductions have cyclic three-primary subgroups. -/
theorem all_three_primary_cyclic (i : Fin 6) :
    IsAddCyclic (AddCommGroup.primaryComponent (SecondReductionData.curve i).toAffine.Point 3) := by
  let : Finite (SecondReductionData.curve i).toAffine.Point := Nat.finite_of_card_ne_zero (by
    rw [SecondReductionData.curve_card]
    fin_cases i <;> decide +kernel)
  fin_cases i
  all_goals first
    | exact three_primary_cyclic 0
    | exact three_primary_cyclic 1
    | (apply three_primary_cyclic_of_nine_not_dvd
       rw [SecondReductionData.curve_card]
       decide +kernel)

end
end Z2Z4Rank6.SecondReductionStructure
