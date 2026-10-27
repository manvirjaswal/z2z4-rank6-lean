module

public import Z2Z4Rank6.SecondBaseFunctionFieldIso
public import Z2Z4Rank6.SecondMathlibFunctionFieldIso

@[expose] public section

/-!
# The G₂ field and Mathlib's printed Jacobian function field

Both component equivalences are constructed by coordinate-ring universal
properties and proved field generation. Source: Jaswal, Theorem 8.1(a),
DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6.SecondBaseMathlibFunctionFieldIso
noncomputable section

def secondFunctionFieldEquivMathlib : SecondFunctionField.K ≃ₐ[ℚ]
    SecondMathlibFunctionFieldIso.MathlibField :=
  SecondBaseFunctionFieldIso.secondBaseFunctionFieldEquiv.trans
    SecondMathlibFunctionFieldIso.mathlibEquivQuadratic.symm

end
end Z2Z4Rank6.SecondBaseMathlibFunctionFieldIso
