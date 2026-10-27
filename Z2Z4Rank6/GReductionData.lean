module

public import Z2Z4Rank6.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Proposition 7.2(b) exact reduction data

The data come from the signed sections in
GFunctionFieldSections and the printed rational G point. Source: M. Jaswal,
DOI 10.5281/zenodo.23437117, Proposition 7.2(b). The checks are in GReductionCheck,
GReductionRational and GReductionRank. Canonical generators choose smaller y;
the selected generators adjust their row signs to give the printed matrix.
-/

namespace Z2Z4Rank6.GReductionData

def primes : Fin 5 → ℕ := ![37, 41, 61, 107, 113]

def orders : Fin 5 → ℕ := ![48, 48, 72, 96, 120]

def multipliers : Fin 5 → ℕ := ![16, 16, 24, 32, 40]

def printedMatrix : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  !![2, 1, 1, 0, 1;
    1, 0, 1, 2, 0;
    0, 2, 0, 0, 2;
    0, 0, 0, 2, 1;
    2, 2, 0, 0, 0]

def signedMatrix : Matrix (Fin 5) (Fin 5) (ZMod 3) :=
  !![1, 2, 2, 0, 2;
    2, 0, 2, 1, 0;
    0, 1, 0, 0, 1;
    0, 0, 0, 1, 2;
    1, 1, 0, 0, 0]

def rowSigns : Fin 5 → ZMod 3 := ![2, 2, 2, 2, 2]

def columnSigns : Fin 5 → ZMod 3 := ![1, 1, 1, 1, 1]

def generatorX : Fin 5 → ℕ := ![27, 39, 36, 42, 72]

def generatorY : Fin 5 → ℕ := ![25, 40, 42, 56, 95]

def canonicalGeneratorX : Fin 5 → ℕ := ![27, 39, 36, 42, 72]

def canonicalGeneratorY : Fin 5 → ℕ := ![12, 1, 19, 51, 18]

def reducedX : Fin 5 → Fin 5 → ℕ :=
  !![30, 17, 1, 13, 28;
    9, 24, 37, 27, 26;
    52, 33, 34, 34, 26;
    96, 12, 64, 28, 78;
    13, 13, 38, 46, 3]

def reducedY : Fin 5 → Fin 5 → ℕ :=
  !![36, 23, 14, 21, 21;
    16, 22, 33, 11, 9;
    44, 16, 51, 10, 55;
    42, 61, 58, 35, 48;
    82, 82, 80, 77, 37]

def a0 : ℤ := 379291648

def b0 : ℤ := 212565977

def rationalX : Fin 5 → ℚ :=
  ![(-85985831567294464 : ℚ) / 1,
    (-58444996670344024 : ℚ) / 1,
    (-2248161523739262976 : ℚ) / 49,
    (-62331445860559616 : ℚ) / 1,
    (-48899358183829504 : ℚ) / 1]

def rationalY : Fin 5 → ℚ :=
  ![(14249583615419300158832640 : ℚ) / 1,
    (-8136347447441088722850120 : ℚ) / 1,
    (606957782636939578644234240 : ℚ) / 343,
    (-9334911353080129534971136 : ℚ) / 1,
    (4153473587131885601894400 : ℚ) / 1]

end Z2Z4Rank6.GReductionData
