import Z2Z4Rank6.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Gusić–Tadić specialization data

The data come from the displayed tables in
Propositions 2.3 and 5.2 of Manvir Jaswal,
DOI 10.5281/zenodo.23437117. Values are the rational polynomial values;
the explicit rational squares certify the printed representatives. The
permutations place unique-prime witnesses first, the m factor next, then the
three positive content primes, and the sign last.
-/

namespace Z2Z4Rank6.GusicTadic

noncomputable section

/-- The eleven nonconstant factors in the printed order of Proposition 2.3. -/
def baseFactors {R : Type*} [CommRing R] (m : R) : Fin 11 → R :=
  ![m-99, m+1, m-11, m+9, m+99, m-1, m+11, m-9,
    m, m^2-99, m^4-2*m^2+9801]

/-- Factor values at m=(14)/3, followed by -1,2,5,7. -/
def base14Values : Fin 15 → ℚ :=
  ![baseFactors ((14)/3 : ℚ) 0, baseFactors ((14)/3 : ℚ) 1, baseFactors ((14)/3 : ℚ) 2, baseFactors ((14)/3 : ℚ) 3, baseFactors ((14)/3 : ℚ) 4, baseFactors ((14)/3 : ℚ) 5, baseFactors ((14)/3 : ℚ) 6, baseFactors ((14)/3 : ℚ) 7, baseFactors ((14)/3 : ℚ) 8, baseFactors ((14)/3 : ℚ) 9, baseFactors ((14)/3 : ℚ) 10, -1, 2, 5, 7]

def base14Representatives : Fin 15 → ℤ :=
  ![-849, 51, -57, 123, 933, 33, 141, -39, 42, -695, 828769, -1, 2, 5, 7]

def base14SquareFactors : Fin 15 → ℚ :=
  ![(1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/9, 1, 1, 1, 1]

/-- The printed representative differs from the computed value by this explicit square. -/
theorem base14_representatives (i : Fin 15) :
    base14Values i=(base14Representatives i : ℚ)*(base14SquareFactors i)^2 := by
  fin_cases i <;> norm_num [base14Values, base14Representatives, base14SquareFactors, baseFactors]

/-- Each printed integer representative is squarefree up to its sign. -/
theorem base14_representatives_squarefree (i : Fin 15) :
    Squarefree (base14Representatives i).natAbs := by
  fin_cases i <;> decide +kernel

def base14Order : Equiv.Perm (Fin 15) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 8, 12, 13, 14, 11] : Fin 15 → Fin 15) (by decide +kernel)

def base14OrderedValues (i : Fin 15) : ℚ := base14Values (base14Order i)

def base14Witnesses : Fin 14 → ℕ := ![283, 17, 19, 41, 311, 11, 47, 13, 139, 73, 3, 2, 5, 7]

/-- Factor values at m=(14)/3, followed by -1,2,5,7. -/
def twist14Values : Fin 16 → ℚ :=
  ![baseFactors ((14)/3 : ℚ) 0, baseFactors ((14)/3 : ℚ) 1, baseFactors ((14)/3 : ℚ) 2, baseFactors ((14)/3 : ℚ) 3, baseFactors ((14)/3 : ℚ) 4, baseFactors ((14)/3 : ℚ) 5, baseFactors ((14)/3 : ℚ) 6, baseFactors ((14)/3 : ℚ) 7, baseFactors ((14)/3 : ℚ) 8, baseFactors ((14)/3 : ℚ) 9, baseFactors ((14)/3 : ℚ) 10, (3*((14)/3 : ℚ)^2+242), -1, 2, 5, 7]

def twist14Representatives : Fin 16 → ℤ :=
  ![-849, 51, -57, 123, 933, 33, 141, -39, 42, -695, 828769, 2766, -1, 2, 5, 7]

def twist14SquareFactors : Fin 16 → ℚ :=
  ![(1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/9, (1)/3, 1, 1, 1, 1]

/-- The printed representative differs from the computed value by this explicit square. -/
theorem twist14_representatives (i : Fin 16) :
    twist14Values i=(twist14Representatives i : ℚ)*(twist14SquareFactors i)^2 := by
  fin_cases i <;> norm_num [twist14Values, twist14Representatives, twist14SquareFactors, baseFactors]

/-- Each printed integer representative is squarefree up to its sign. -/
theorem twist14_representatives_squarefree (i : Fin 16) :
    Squarefree (twist14Representatives i).natAbs := by
  fin_cases i <;> decide +kernel

def twist14Order : Equiv.Perm (Fin 16) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 8, 13, 14, 15, 12] : Fin 16 → Fin 16) (by decide +kernel)

def twist14OrderedValues (i : Fin 16) : ℚ := twist14Values (twist14Order i)

def twist14Witnesses : Fin 15 → ℕ := ![283, 17, 19, 41, 311, 11, 47, 13, 139, 73, 461, 3, 2, 5, 7]

/-- Factor values at m=(50)/3, followed by -1,2,5,7. -/
def twist50Values : Fin 16 → ℚ :=
  ![baseFactors ((50)/3 : ℚ) 0, baseFactors ((50)/3 : ℚ) 1, baseFactors ((50)/3 : ℚ) 2, baseFactors ((50)/3 : ℚ) 3, baseFactors ((50)/3 : ℚ) 4, baseFactors ((50)/3 : ℚ) 5, baseFactors ((50)/3 : ℚ) 6, baseFactors ((50)/3 : ℚ) 7, baseFactors ((50)/3 : ℚ) 8, baseFactors ((50)/3 : ℚ) 9, baseFactors ((50)/3 : ℚ) 10, (2*((50)/3 : ℚ)^2+243), -1, 2, 5, 7]

def twist50Representatives : Fin 16 → ℤ :=
  ![-741, 159, 51, 231, 1041, 141, 249, 69, 6, 1609, 6998881, 7187, -1, 2, 5, 7]

def twist50SquareFactors : Fin 16 → ℚ :=
  ![(1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (5)/3, (1)/3, (1)/9, (1)/3, 1, 1, 1, 1]

/-- The printed representative differs from the computed value by this explicit square. -/
theorem twist50_representatives (i : Fin 16) :
    twist50Values i=(twist50Representatives i : ℚ)*(twist50SquareFactors i)^2 := by
  fin_cases i <;> norm_num [twist50Values, twist50Representatives, twist50SquareFactors, baseFactors]

/-- Each printed integer representative is squarefree up to its sign. -/
theorem twist50_representatives_squarefree (i : Fin 16) :
    Squarefree (twist50Representatives i).natAbs := by
  fin_cases i <;> decide +kernel

def twist50Order : Equiv.Perm (Fin 16) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 8, 13, 14, 15, 12] : Fin 16 → Fin 16) (by decide +kernel)

def twist50OrderedValues (i : Fin 16) : ℚ := twist50Values (twist50Order i)

def twist50Witnesses : Fin 15 → ℕ := ![13, 53, 17, 11, 347, 47, 83, 23, 1609, 113, 7187, 3, 2, 5, 7]

/-- Factor values at m=(50)/3, followed by -1,2,5,7. -/
def product50Values : Fin 17 → ℚ :=
  ![baseFactors ((50)/3 : ℚ) 0, baseFactors ((50)/3 : ℚ) 1, baseFactors ((50)/3 : ℚ) 2, baseFactors ((50)/3 : ℚ) 3, baseFactors ((50)/3 : ℚ) 4, baseFactors ((50)/3 : ℚ) 5, baseFactors ((50)/3 : ℚ) 6, baseFactors ((50)/3 : ℚ) 7, baseFactors ((50)/3 : ℚ) 8, baseFactors ((50)/3 : ℚ) 9, baseFactors ((50)/3 : ℚ) 10, (2*((50)/3 : ℚ)^2+243), (3*((50)/3 : ℚ)^2+242), -1, 2, 5, 7]

def product50Representatives : Fin 17 → ℤ :=
  ![-741, 159, 51, 231, 1041, 141, 249, 69, 6, 1609, 6998881, 7187, 9678, -1, 2, 5, 7]

def product50SquareFactors : Fin 17 → ℚ :=
  ![(1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (1)/3, (5)/3, (1)/3, (1)/9, (1)/3, (1)/3, 1, 1, 1, 1]

/-- The printed representative differs from the computed value by this explicit square. -/
theorem product50_representatives (i : Fin 17) :
    product50Values i=(product50Representatives i : ℚ)*(product50SquareFactors i)^2 := by
  fin_cases i <;> norm_num [product50Values, product50Representatives, product50SquareFactors, baseFactors]

/-- Each printed integer representative is squarefree up to its sign. -/
theorem product50_representatives_squarefree (i : Fin 17) :
    Squarefree (product50Representatives i).natAbs := by
  fin_cases i <;> decide +kernel

def product50Order : Equiv.Perm (Fin 17) :=
  Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 8, 14, 15, 16, 13] : Fin 17 → Fin 17) (by decide +kernel)

def product50OrderedValues (i : Fin 17) : ℚ := product50Values (product50Order i)

def product50Witnesses : Fin 16 → ℕ := ![13, 53, 17, 11, 347, 47, 83, 23, 1609, 113, 7187, 1613, 3, 2, 5, 7]

end

end Z2Z4Rank6.GusicTadic
