module

public import Z2Z4Rank6.BaseCurve
public import Z2Z4Rank6.BaseLocalMaps

@[expose] public section

/-!
# The rational point map from E_C to C

The inverse quartic parametrization in Lemma 4.1 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117. On the regular affine chart this is the
coordinate map. On the three-point complement it is extended by the
printed base point. Injectivity is asserted only on the regular chart.
-/

namespace Z2Z4Rank6

/-- Extend the inverse quartic parametrization to a total map on E_C(ℚ). -/
noncomputable def ecToCPoint (P : RationalPoints EC) : CPoint := by
  classical
  exact if h : ecQuarticChart P then quarticToC (ecToQuartic ⟨P, h⟩) else baseC0

theorem ecToCPoint_on_chart (P : RationalPoints EC) (h : ecQuarticChart P) :
    ecToCPoint P=quarticToC (ecToQuartic ⟨P, h⟩) := by
  simp [ecToCPoint, h]

/-- The rational map is injective wherever its printed denominators are nonzero. -/
theorem ecToCPoint_injOn : Set.InjOn ecToCPoint {P | ecQuarticChart P} := by
  intro P hP Q hQ h
  rw [ecToCPoint_on_chart P hP, ecToCPoint_on_chart Q hQ] at h
  exact congrArg Subtype.val (ecToQuartic_injective (quarticToC_injective h))

/-- On an affine elliptic-curve point in the regular chart, the three
coordinates are the printed field-valued quartic formulas. -/
theorem ecToCPoint_some_coordinates (x y : ℚ) (h : EC.toAffine.Nonsingular x y)
    (hx : x+82 ≠ 0) :
    ((ecToCPoint (.some x y h)).m,
      ((ecToCPoint (.some x y h)).u, (ecToCPoint (.some x y h)).v)) =
        ecCoordinatesToC (x,y) := by
  rw [ecToCPoint_on_chart (.some x y h) hx]
  rfl

/-- Extension of the rational coordinates to any field commutes with the
same coordinate formulas. This applies in particular to ℚ → ℚ_p. -/
theorem map_ecToCPoint_some_coordinates {K : Type*} [Field K] (f : ℚ →+* K)
    (x y : ℚ) (h : EC.toAffine.Nonsingular x y) (hx : x+82 ≠ 0) :
    (f (ecToCPoint (.some x y h)).m,
      (f (ecToCPoint (.some x y h)).u, f (ecToCPoint (.some x y h)).v)) =
        ecCoordinatesToC (f x, f y) := by
  have he := congrArg (Prod.map f (Prod.map f f)) (ecToCPoint_some_coordinates x y h hx)
  rw [map_ecCoordinatesToC] at he
  exact he

/-- At the affine point corresponding to c₀, the point map returns c₀. -/
theorem ecToCPoint_ecC0 : ecToCPoint ecC0=baseC0 := by
  have he : ((ecToCPoint ecC0).m, ((ecToCPoint ecC0).u, (ecToCPoint ecC0).v)) =
      ecCoordinatesToC (ecCoordinatesC0 (K := ℚ)) :=
    ecToCPoint_some_coordinates _ _ _ (by norm_num)
  rw [ecCoordinatesToC_c0] at he
  apply CPoint.ext
  · exact congrArg Prod.fst he
  · exact congrArg (fun z => z.2.1) he
  · exact congrArg (fun z => z.2.2) he

end Z2Z4Rank6
