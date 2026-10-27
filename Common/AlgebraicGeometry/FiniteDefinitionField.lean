module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.FinTrdeg

@[expose] public section

/-!
# Algebraically closed fields containing finite definition fields

The relative algebraic closure of a finitely generated intermediate
field inside an algebraically closed extension is algebraically closed
and has finite transcendence degree over the original field. These are
proved field-theoretic facts.
-/
namespace Common.AlgebraicGeometry.FiniteDefinitionField
noncomputable section
variable (k K : Type) [Field k] [Field K] [Algebra k K] [IsAlgClosed K]

abbrev closure (L : IntermediateField k K) := algebraicClosure L K

instance closure_isAlgClosed (L : IntermediateField k K) : IsAlgClosed (closure k K L) :=
  IsAlgClosure.isAlgClosed L

omit [IsAlgClosed K] in
theorem closure_finite_trdeg (L : IntermediateField k K) (hL : L.FG) :
    Algebra.trdeg k (closure k K L)<Cardinal.aleph0 := by
  let : Algebra.EssFiniteType k L := IntermediateField.essFiniteType_iff.mpr hL
  let : FinTrdeg k (closure k K L) := FinTrdeg.trans k L (closure k K L)
  exact trdeg_lt_aleph0 k (closure k K L)

end
end Common.AlgebraicGeometry.FiniteDefinitionField
