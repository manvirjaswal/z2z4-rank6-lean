module

public import Common.AlgebraicGeometry.ModuleSheafCohomology
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

/-!
# Conormal sheaves and their degrees on curves

The ideal is the kernel of O_X -> i_*O_C. Pulling it back to C
is the conormal sheaf I/I^2 for a closed immersion. Its degree on a
proper curve is chi(I/I^2)-chi(O_C), with cohomology and explicit
finite-dimensionality retained. For a smooth divisor on a smooth
surface, its self-intersection is the negative of this degree.

References: Stacks Section 29.32 (tag 01R1), conormal sheaves;
Section 53.5 (tag 0B5B), degree and Euler characteristic.
-/
namespace Common.AlgebraicGeometry.ConormalDegree
noncomputable section
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ModuleSheafCohomology
set_option backward.isDefEq.respectTransparency false
variable {C X : Scheme.{0}} (i : C ⟶ X)

def structureRestriction : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit C.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

def ideal : X.Modules := kernel (structureRestriction i)

def conormal : C.Modules := (Scheme.Modules.pullback i).obj (ideal i)

variable (k : Type) [Field k] (s : C ⟶ Spec (CommRingCat.of k))

def degree : ℤ := euler01 k C s (conormal i)-euler01 k C s (SheafOfModules.unit C.ringCatSheaf)

def HasFiniteCohomology : Prop :=
  HasFiniteCohomology01 k C s (conormal i) ∧
    HasFiniteCohomology01 k C s (SheafOfModules.unit C.ringCatSheaf)

/-- A conormal degree equal to one, with finiteness included. -/
def HasDegreeOne : Prop := HasFiniteCohomology i k s ∧ degree i k s=1

theorem degree_eq (n : ℤ) (h : degree i k s=n) :
    euler01 k C s (conormal i)=euler01 k C s (SheafOfModules.unit C.ringCatSheaf)+n := by
  unfold degree at h
  linarith

end
end Common.AlgebraicGeometry.ConormalDegree
