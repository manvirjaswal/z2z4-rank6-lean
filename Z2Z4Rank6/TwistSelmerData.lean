import Z2Z4Rank6.GusicTadicModels
import Z2Z4Rank6.SplitDescentImage

/-!
# Integral split models for the three twist fibers

Exact arithmetic for Proposition 5.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117. The twists are specialized at 14/3, 50/3,
and 50/3. The last two models interchange the two negative roots so that
r₂>r₃; this leaves the Weierstrass equation unchanged.
-/

namespace Z2Z4Rank6.TwistSelmer

noncomputable section

/-- The squarefree rational twist classes, in the order q₁,q₂,q₁₂. -/
def D : Fin 3 → ℤ := ![13830,35935,69555786]
def A : Fin 3 → ℤ := ![3747769,31133881,31133881]
def B : Fin 3 → ℤ := ![2090231,17136119,17136119]
def C : Fin 3 → ℕ := ![2*3*5*7*73*139*11353,2*3*5*113*241*257*1609,
  2*3*5*113*241*257*1609]
def parameter : Fin 3 → ℚ := ![14/3,50/3,50/3]
def twistPolynomial : Fin 3 → Polynomial ℤ :=
  ![GusicTadic.q1Poly,GusicTadic.q2Poly,GusicTadic.q12Poly]
def scale : Fin 3 → ℚ := ![7/243,7/243,7/729]
def twistSquareScale : Fin 3 → ℚ := ![1/3,1/3,1/9]

def r2 (k : Fin 3) : ℤ := D k*(A k)^2
def r3 (k : Fin 3) : ℤ := D k*(B k)^2

/-- The normalized split rational curve y²=x(x+r₂)(x+r₃). -/
def curve (k : Fin 3) : WeierstrassCurve ℚ :=
  splitWeierstrass 0 (-(r2 k : ℚ)) (-(r3 k : ℚ))

theorem raw_a_values : (fun k => a (parameter k))=
    ![(26234383/81 : ℚ),-119952833/81,-119952833/81] := by
  funext k
  fin_cases k <;> norm_num [parameter,a]

theorem raw_b_values : (fun k => b (parameter k))=
    ![(14631617/81 : ℚ),-217937167/81,-217937167/81] := by
  funext k
  fin_cases k <;> norm_num [parameter,b]

theorem twist_squareclass_factor (k : Fin 3) :
    GusicTadic.evalAt (parameter k) (twistPolynomial k)=
      (D k : ℚ)*(twistSquareScale k)^2 := by
  fin_cases k <;> norm_num [parameter,twistPolynomial,D,twistSquareScale,
    GusicTadic.evalAt,GusicTadic.q1Poly,GusicTadic.q2Poly,GusicTadic.q12Poly,q1,q2,q12]

theorem D_factorization : D=![2*3*5*461,5*7187,2*3*1613*7187] := by
  decide

theorem A_factorization : A=![17*19*41*283,23*47*83*347,23*47*83*347] := by
  decide

theorem B_factorization : B=![11*13*47*311,7*11*13*17*19*53,7*11*13*17*19*53] := by
  decide

theorem difference_factorization (k : Fin 3) :
    (A k)^2-(B k)^2=![2^5*3*5^3*7*73*139*11353,
      2^5*3*5^4*113*241*257*1609,2^5*3*5^4*113*241*257*1609] k := by
  fin_cases k <;> norm_num [A,B]

theorem scale_ne_zero (k : Fin 3) : scale k ≠ 0 := by
  fin_cases k <;> norm_num [scale]

theorem roots_nonzero_distinct (k : Fin 3) : r2 k ≠ 0 ∧ r3 k ≠ 0 ∧ r2 k ≠ r3 k := by
  fin_cases k <;> norm_num [r2,r3,D,A,B]

theorem roots_ordered (k : Fin 3) : 0 < r3 k ∧ r3 k < r2 k := by
  fin_cases k <;> norm_num [r2,r3,D,A,B]

theorem curve_eq_twistModel (k : Fin 3) : curve k=
    GusicTadic.twistModel (D k : ℚ) (A k) (B k) := by
  apply WeierstrassCurve.ext <;>
    simp [curve,splitWeierstrass,GusicTadic.twistModel,r2,r3] <;> ring

/-- The normalized integer model is isomorphic to the rational fiber
by the displayed admissible scaling (x,y)↦(scale²x,scale³y). -/
theorem normalized_scaling (k : Fin 3) :
    scalingChange (Units.mk0 (scale k) (scale_ne_zero k)) • curve k=
      GusicTadic.fiberModel (twistPolynomial k) (parameter k) := by
  fin_cases k <;> ext <;>
    norm_num [scalingChange,curve,splitWeierstrass,r2,r3,D,A,B,scale,
      GusicTadic.fiberModel,GusicTadic.twistModel,parameter,twistPolynomial,
      GusicTadic.evalAt,GusicTadic.q1Poly,GusicTadic.q2Poly,GusicTadic.q12Poly,
      q1,q2,q12,a,b,WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,WeierstrassCurve.variableChange_a₆]

instance curveElliptic (k : Fin 3) : (curve k).IsElliptic := by
  rw [curve_eq_twistModel]
  constructor
  rw [isUnit_iff_ne_zero,GusicTadic.twistModel_discriminant]
  fin_cases k <;> norm_num [D,A,B,E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

theorem supports_coprime (k : Fin 3) :
    (A k).natAbs.Coprime (B k).natAbs ∧ (A k).natAbs.Coprime (C k) ∧
      (B k).natAbs.Coprime (C k) := by
  fin_cases k <;> norm_num [A,B,C,Nat.Coprime]

/-- Squarefree root-product divisors have the exact refined twist supports. -/
theorem supports (k : Fin 3) (d : ECFullTriple)
    (h : d ∈ fullTwoSelmerTriples (r2 k) (r3 k)) :
    d.1 ∣ D k*A k*B k ∧
      d.2.1 ∣ D k*A k*(C k : ℤ) ∧ d.2.2 ∣ D k*B k*(C k : ℤ) := by
  refine ⟨?_,?_,?_⟩
  · apply (h.1.dvd_pow_iff_dvd (by decide : 2≠0)).mp
    apply h.2.2.2.1.trans
    refine ⟨1,?_⟩
    dsimp [r2,r3]
    ring
  · apply (h.2.1.dvd_pow_iff_dvd (by decide : 5≠0)).mp
    apply h.2.2.2.2.1.trans
    fin_cases k <;> norm_num [r2,r3,D,A,B,C]
  · apply (h.2.2.1.dvd_pow_iff_dvd (by decide : 5≠0)).mp
    apply h.2.2.2.2.2.1.trans
    fin_cases k <;> norm_num [r2,r3,D,A,B,C]

set_option maxRecDepth 30000 in
/-- The three normalized twist representatives are squarefree. -/
theorem D_squarefree (k : Fin 3) : Squarefree (D k) := by
  apply Int.squarefree_natAbs.mp
  fin_cases k <;> decide +kernel


end
end Z2Z4Rank6.TwistSelmer
