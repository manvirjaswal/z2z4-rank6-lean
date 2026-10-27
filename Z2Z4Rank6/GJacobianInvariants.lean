module

public import Z2Z4Rank6.GProjectiveQuartic
public import Common.Elliptic.BinaryQuarticJacobianTheorem
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

/-!
# The invariant cubic and printed model for G

Jaswal, Proposition 7.2(a), DOI 10.5281/zenodo.23437117. This file proves
the admissible change X=12²x+48, Y=12³y between CFS's invariant
cubic and the printed equation.
-/

namespace Z2Z4Rank6.GJacobianInvariants
noncomputable section
open BinaryQuarticModel

def modelChange : WeierstrassCurve.VariableChange ℚ :=
  ⟨Units.mk0 12 (by norm_num),48,0,0⟩

theorem variableChange_eq : modelChange • invariantCurve GProjectiveQuartic.model = JG := by
  ext <;> norm_num [modelChange,invariantCurve,c4,c6,invariantI,invariantJ,
    GProjectiveQuartic.model,JG,WeierstrassCurve.variableChange_def]

end
end Z2Z4Rank6.GJacobianInvariants
