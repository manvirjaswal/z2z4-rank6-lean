module

public import Z2Z4Rank6.FamilyIdentities
public import Z2Z4Rank6.Quartic
public import Z2Z4Rank6.Statements
public import Z2Z4Rank6.VariableChangePoints
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Tactic

@[expose] public section

/-!
# The conic fiber and the Dujella–Peral minimal equation

The exact parameter values, equations, admissible model changes and point-group
equivalence are proved here. Source: Jaswal, Proposition 7.1(b),
DOI 10.5281/zenodo.23437117; Dujella–Peral, Construction of high rank
elliptic curves, Journal of Geometric Analysis 31 (2021), Section 7.2,
author manuscript page 19:
https://web.math.pmf.unizg.hr/~duje/pdf/DujellaPeralConstruction.pdf
-/

namespace Z2Z4Rank6.ConicRankNine

noncomputable section

/-- The minimal equation printed by Dujella and Peral in §7.2. -/
def publishedModel : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := 0
  a₃ := 0
  a₄ := -1443705842368492991301675445569878391286260
  a₆ := 518524534126954116322153225511662398609137586525877978241619600

/-- The rational value of m on the conic at the printed k. -/
theorem conic_parameter : conicM (25/11 : ℚ) = 1681/119 := by
  norm_num [conicM]

/-- This is the same Dujella–Peral base parameter t=900/781. -/
theorem dp_parameter : parameterM (900/781 : ℚ) = 1681/119 := by
  norm_num [parameterM]

def integralFiber : WeierstrassCurve ℚ := E 46529164800 95880799729

def fiberToIntegral : WeierstrassCurve.VariableChange ℚ :=
  ⟨Units.mk0 (-400/28647703) (by norm_num), 0, 0, 0⟩

def integralToPublished : WeierstrassCurve.VariableChange ℚ :=
  ⟨Units.mk0 2 (by norm_num), -3786030311219388504480, 1, 0⟩

/-- Exact admissible change from the rational fiber to its integral model. -/
theorem fiber_integral_change : fiberToIntegral • X (1681/119 : ℚ) = integralFiber := by
  ext <;> norm_num [fiberToIntegral, integralFiber,
    WeierstrassCurve.variableChange_def, X, E, a, b]

/-- Exact admissible change to the previously published equation. -/
theorem integral_published_change : integralToPublished • integralFiber = publishedModel := by
  ext <;> norm_num [integralToPublished, integralFiber, publishedModel,
    WeierstrassCurve.variableChange_def, E]

/-- The k=25/11 fiber is the curve printed in §7.2 of Dujella–Peral. -/
theorem conic_published_change :
    (integralToPublished * fiberToIntegral) • X (conicM (25/11 : ℚ)) = publishedModel := by
  rw [conic_parameter, mul_smul, fiber_integral_change, integral_published_change]

instance publishedModel_isElliptic : publishedModel.IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, publishedModel, isUnit_iff_ne_zero]

instance fiber_isElliptic : (X (1681/119 : ℚ)).IsElliptic := by
  constructor
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, X, E, a, b, isUnit_iff_ne_zero]

/-- The coefficient change induces an equivalence of the point groups. -/
def fiberPublishedEquiv : RationalPoints (X (1681/119 : ℚ)) ≃+ RationalPoints publishedModel :=
  (VariableChangePoints.pointEquiv (X (1681/119 : ℚ))
    (integralToPublished * fiberToIntegral)).symm.trans
    (PointScaling.pointCongr (by
      rw [mul_smul,fiber_integral_change,integral_published_change]))

end
end Z2Z4Rank6.ConicRankNine
