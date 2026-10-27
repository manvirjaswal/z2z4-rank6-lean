module

public import Z2Z4Rank6.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Printed reduction data for Proposition 5.1

Computed with Python from the signed point formulas in
Manvir Jaswal, DOI 10.5281/zenodo.23437117, Lemmas 2.2, 3.2,
Proposition 4.2 and Proposition 5.1. The checks are in ReductionCheck.
The explicit row and column signs reconcile the printed matrix with those
signed coordinate formulas and the generators chosen below.
-/

namespace Z2Z4Rank6
namespace ReductionData

def primes : Fin 6 → ℕ := ![23, 37, 53, 83, 89, 113]

def orders : Fin 6 → ℕ := ![24, 48, 48, 96, 96, 96]

def multipliers : Fin 6 → ℕ := ![8, 16, 16, 32, 32, 32]

def printedMatrix : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 1, 1, 0;
    1, 1, 0, 0, 1, 1;
    2, 0, 1, 0, 0, 2;
    2, 2, 1, 1, 0, 1;
    2, 0, 2, 2, 1, 0;
    2, 0, 2, 1, 1, 0]

def signedMatrix : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 0, 1, 1, 1, 0;
    2, 2, 0, 0, 2, 2;
    2, 0, 1, 0, 0, 2;
    1, 1, 2, 2, 0, 2;
    1, 0, 1, 1, 2, 0;
    1, 0, 1, 2, 2, 0]

def rowSigns : Fin 6 → ZMod 3 := ![1, 2, 1, 2, 2, 2]

def columnSigns : Fin 6 → ZMod 3 := ![1, 1, 1, 1, 1, 1]

def generatorX : Fin 6 → ℕ := ![9, 11, 40, 75, 79, 4]

def generatorY : Fin 6 → ℕ := ![10, 25, 11, 63, 54, 95]

def reducedX : Fin 6 → Fin 6 → ℕ :=
  !![17, 5, 17, 17, 17, 7;
    4, 22, 7, 7, 4, 18;
    4, 31, 34, 31, 25, 27;
    66, 79, 44, 68, 40, 82;
    57, 88, 21, 21, 21, 73;
    99, 81, 39, 39, 39, 31]

def reducedY : Fin 6 → Fin 6 → ℕ :=
  !![11, 0, 11, 11, 11, 19;
    1, 23, 0, 0, 1, 6;
    12, 17, 36, 17, 0, 16;
    44, 67, 79, 4, 8, 57;
    81, 0, 9, 9, 80, 62;
    50, 0, 93, 20, 20, 91]

def a0 : ℤ := 7037226227200

def b0 : ℤ := 3329722383911

def rationalX : Fin 6 → ℚ :=
  ![(-9134182662998624112839888896 : ℚ) / 625,
    (-20409047029579692378895000 : ℚ) / 1,
    (-19944153128696423007969280 : ℚ) / 1,
    (-80466963140208120656325184314880 : ℚ) / 5755201,
    (6804553116957406970610499537448960 : ℚ) / 6086089,
    (-224941667455133109155372655848800 : ℚ) / 6355441]

def rationalY : Fin 6 → ℚ :=
  ![(662855215902654331319766085126147257864192 : ℚ) / 15625,
    (-74424010688654073526392146467669035000 : ℚ) / 1,
    (72283797432626184699428097150904442880 : ℚ) / 1,
    (-523630354101388083657619121342854157760049835520 : ℚ) / 13806727199,
    (576439127971694303193998201509676740930408320430080 : ℚ) / 15014381563,
    (-1766434583488622221272564141293802229577069647200 : ℚ) / 16022066761]

end ReductionData
end Z2Z4Rank6
