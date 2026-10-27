module

public import Z2Z4Rank6.GReductionCheck
public import Z2Z4Rank6.ReductionCheckCounts
public import Common.Elliptic.FiniteAbelianCertificates

@[expose] public section

/-!
# The reduction group at 61 in Proposition 7.2(b)

The finite-field point group of E_{379291648,212565977} is
Z/36 × Z/2. Generators (7,11) and (41,0) give a kernel-checked certificate
with 72 residues. The three-primary subgroup is cyclic.
-/
namespace Z2Z4Rank6.GReductionStructure
noncomputable section
open Common.WeierstrassCoordinates Common.FiniteAbelianCertificates

abbrev C := GReductionData.curve 2
abbrev Group := C.toAffine.Point

def P : Group := .mk (x:=7) (y:=11) (by
  rw [WeierstrassCurve.Affine.equation_iff]
  decide +kernel)

def T : Group := .mk (x:=41) (y:=0) (by
  rw [WeierstrassCurve.Affine.equation_iff]
  decide +kernel)

theorem P_mul : 36 • P=0 := by
  apply encode_injective C
  rw [encode_nsmul]
  change coordinateMul C 36 (some (7,11))=none
  decide +kernel

theorem T_mul : 2 • T=0 := by
  apply encode_injective C
  rw [encode_nsmul]
  change coordinateMul C 2 (some (41,0))=none
  decide +kernel

theorem kernel_certificate : ∀ a : Fin 36, ∀ b : Fin 2,
    coordinateAdd C (coordinateMul C a.val (some (7,11)))
      (coordinateMul C b.val (some (41,0)))=none → a.val=0 ∧ b.val=0 := by
  decide +kernel

theorem kernel_zero (a : Fin 36) (b : Fin 2) (h : a.val • P+b.val • T=0) :
    a.val=0 ∧ b.val=0 := by
  have hc := congrArg encode h
  rw [encode_add,encode_nsmul,encode_nsmul] at hc
  exact kernel_certificate a b hc

/-- Additive equivalence with the printed finite group. -/
def groupEquiv : Group ≃+ (ZMod 36 × ZMod 2) :=
  (productEquiv 36 2 P T P_mul T_mul kernel_zero
    (GReductionData.curve_card 2)).symm

theorem group_structure_at_61 : Nonempty (Group ≃+ (ZMod 36 × ZMod 2)) := ⟨groupEquiv⟩

theorem three_primary_cyclic_at_61 : IsAddCyclic (AddCommGroup.primaryComponent Group 3) :=
  three_primary_cyclic groupEquiv

/-- All five printed reductions have cyclic three-primary subgroups. -/
theorem all_three_primary_cyclic (i : Fin 5) :
    IsAddCyclic (AddCommGroup.primaryComponent (GReductionData.curve i).toAffine.Point 3) := by
  let : Finite (GReductionData.curve i).toAffine.Point := Nat.finite_of_card_ne_zero (by
    rw [GReductionData.curve_card]
    fin_cases i <;> decide +kernel)
  fin_cases i
  all_goals first
    | exact three_primary_cyclic_at_61
    | (apply three_primary_cyclic_of_nine_not_dvd
       rw [GReductionData.curve_card]
       decide +kernel)

end
end Z2Z4Rank6.GReductionStructure

namespace Z2Z4Rank6.ReductionData

/-- Proposition 5.1: all six printed first-family reductions have cyclic
three-primary subgroups, as nine divides none of their group orders. -/
theorem three_primary_cyclic (i : Fin 6) :
    IsAddCyclic (AddCommGroup.primaryComponent (curve i).toAffine.Point 3) := by
  let : Finite (curve i).toAffine.Point := Nat.finite_of_card_ne_zero (by
    rw [curve_card]
    fin_cases i <;> decide +kernel)
  apply Common.FiniteAbelianCertificates.three_primary_cyclic_of_nine_not_dvd
  exact (three_primary_orders i).2

end Z2Z4Rank6.ReductionData
