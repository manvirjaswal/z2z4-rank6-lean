module

public import Z2Z4Rank6.GProjectiveQuartic
public import Common.Elliptic.BinaryQuarticPoints

@[expose] public section

/-!
# The printed rational point on the complete G

Jaswal, Proposition 7.2(a), DOI 10.5281/zenodo.23437117. The point
(m,η)=(57,31836) is a Spec Q morphism into the complete weighted
Proj, obtained by evaluation at (57:1:31836), with its base equation.
-/

namespace Z2Z4Rank6.GProjectiveQuartic
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem printedPoint_equation : BinaryQuarticModel.Equation model 57 31836 := by
  norm_num [BinaryQuarticModel.Equation,model]

def printedPoint : Spec (CommRingCat.of ℚ) ⟶ scheme :=
  BinaryQuarticModel.affinePointMorphism model 57 31836 printedPoint_equation

theorem printedPoint_over : printedPoint ≫ structureMap = 𝟙 (Spec (CommRingCat.of ℚ)) :=
  BinaryQuarticModel.affinePointMorphism_over model 57 31836 printedPoint_equation

theorem rational_point_exists :
    Nonempty {p : Spec (CommRingCat.of ℚ) ⟶ scheme //
      p ≫ structureMap = 𝟙 (Spec (CommRingCat.of ℚ))} :=
  ⟨printedPoint,printedPoint_over⟩

end
end Z2Z4Rank6.GProjectiveQuartic
