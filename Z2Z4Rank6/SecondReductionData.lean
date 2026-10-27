import Z2Z4Rank6.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Section 8(d) exact reduction data

The data come from the signed sections in
SecondSections and the printed rational G₂ point. Source: M. Jaswal,
DOI 10.5281/zenodo.23437117, Section 8(d). The checks are in SecondReductionCheck,
SecondReductionRational and SecondReductionRank. Canonical generators choose smaller y;
the selected generators adjust their row signs to give the printed matrix.
-/

namespace Z2Z4Rank6.SecondReductionData

def primes : Fin 6 → ℕ := ![41, 47, 59, 67, 79, 97]

def orders : Fin 6 → ℕ := ![48, 48, 72, 72, 96, 96]

def multipliers : Fin 6 → ℕ := ![16, 16, 24, 24, 32, 32]

def printedMatrix : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 1, 1, 1, 1, 2;
    1, 0, 1, 2, 1, 0;
    0, 2, 2, 0, 0, 0;
    2, 2, 1, 0, 0, 1;
    2, 1, 0, 1, 1, 1;
    1, 2, 1, 1, 0, 2]

def signedMatrix : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  !![1, 1, 1, 1, 1, 2;
    2, 0, 2, 1, 2, 0;
    0, 2, 2, 0, 0, 0;
    2, 2, 1, 0, 0, 1;
    2, 1, 0, 1, 1, 1;
    2, 1, 2, 2, 0, 1]

def rowSigns : Fin 6 → ZMod 3 := ![1, 2, 1, 1, 1, 2]

def columnSigns : Fin 6 → ZMod 3 := ![1, 1, 1, 1, 1, 1]

def generatorX : Fin 6 → ℕ := ![31, 6, 21, 24, 32, 81]

def generatorY : Fin 6 → ℕ := ![16, 33, 25, 4, 15, 70]

def canonicalGeneratorX : Fin 6 → ℕ := ![31, 6, 21, 24, 32, 81]

def canonicalGeneratorY : Fin 6 → ℕ := ![16, 14, 25, 4, 15, 27]

def reducedX : Fin 6 → Fin 6 → ℕ :=
  !![16, 11, 39, 26, 19, 31;
    12, 2, 37, 12, 40, 9;
    16, 26, 50, 41, 21, 21;
    21, 28, 13, 42, 5, 65;
    23, 15, 71, 24, 68, 64;
    65, 44, 64, 31, 93, 8]

def reducedY : Fin 6 → Fin 6 → ℕ :=
  !![7, 39, 29, 32, 5, 25;
    21, 42, 8, 26, 13, 25;
    45, 4, 3, 13, 34, 34;
    29, 14, 1, 33, 0, 14;
    2, 73, 35, 45, 15, 9;
    30, 43, 62, 28, 0, 1]

def a0 : ℤ := 460019200

def b0 : ℤ := 11180308689

def rationalX : Fin 6 → ℚ :=
  ![(499284308691438490000 : ℚ) / 9,
    (2215757908015311217546474200 : ℚ) / 19037652529,
    (339558475170049273921536 : ℚ) / 3258025,
    (291785582846327357358433632 : ℚ) / 113273449,
    (-4563185528671931392 : ℚ) / 1,
    (3381199714987226818560000 : ℚ) / 83521]

def rationalY : Fin 6 → ℚ :=
  ![(20160664931462925833681385250000 : ℚ) / 27,
    (5740784385308762492415425120654125547982600 : ℚ) / 2626758182993833,
    (11933832350789075906470717518685372416 : ℚ) / 5880735125,
    (-36488427911205899155665230417948954647008 : ℚ) / 1205569317707,
    (48902979030030781451001744384 : ℚ) / 1,
    (-12603085399516700402992840055040000000 : ℚ) / 24137569]

end Z2Z4Rank6.SecondReductionData
