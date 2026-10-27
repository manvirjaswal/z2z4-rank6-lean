import Z2Z4Rank6.GusicTadicSpecialization

/-!
# Coordinate compatibility of canonical specialization

The point maps in the Gusić–Tadić applications act on the three
polynomial sections of Lemma 2.2 of M. Jaswal,
DOI 10.5281/zenodo.23437117, by the printed rational specialization.
-/

namespace Z2Z4Rank6.GusicTadic

open Polynomial Common.WeierstrassCoordinates
noncomputable section

/-- Polynomial coordinates specialize by ordinary polynomial evaluation. -/
theorem CanonicalSpecializationAt.polynomial_coordinates
    {W : WeierstrassCurve RF} {V : WeierstrassCurve ℚ} {r : ℚ}
    {σ : W.toAffine.Point →+ V.toAffine.Point} (hσ : CanonicalSpecializationAt W V r σ)
    (p q : ℚ[X])
    (h : W.toAffine.Nonsingular (algebraMap ℚ[X] RF p) (algebraMap ℚ[X] RF q)) :
    encode (σ (.some _ _ h)) = some (p.eval r,q.eval r) := by
  simpa [RegularAt, RatFunc.eval] using hσ _ _ h

def primaryX {R : Type*} [CommRing R] (m : R) : Fin 3 → R :=
  ![p1x m,p2x m,p3x m]

def primaryY {R : Type*} [CommRing R] (m : R) : Fin 3 → R :=
  ![p1y m,p2y m,p3y m]

private theorem primaryX_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : R) (j : Fin 3) :
    f (primaryX m j)=primaryX (f m) j := by
  fin_cases j <;> simp [primaryX, p1x, p2x, p3x, map_ofNat]

private theorem primaryY_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (m : R) (j : Fin 3) :
    f (primaryY m j)=primaryY (f m) j := by
  fin_cases j <;> simp [primaryY, p1y, p2y, p3y, map_ofNat]

theorem original_points_coordinates (j : Fin 3) :
    encode (RationalFunctionFamily.points j) =
      some (primaryX (RatFunc.X : RF) j,primaryY (RatFunc.X : RF) j) := by
  fin_cases j <;> rfl

/-- The canonical map sends the three generic points to their printed
specialized coordinates. -/
theorem CanonicalSpecializationAt.primary_points_coordinates
    {r : ℚ} {σ : RationalFunctionFamily.curve.toAffine.Point →+ (X r).toAffine.Point}
    (hσ : CanonicalSpecializationAt _ _ r σ) (j : Fin 3) :
    encode (σ (RationalFunctionFamily.points j)) = some (primaryX r j,primaryY r j) := by
  have hp := original_points_coordinates j
  cases hP : RationalFunctionFamily.points j with
  | zero => simp [hP, encode] at hp
  | some x y h =>
    rw [hP] at hp
    have hxy := Option.some.inj hp
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    have hpx : algebraMap ℚ[X] RF (primaryX (Polynomial.X : ℚ[X]) j)=x := by
      rw [primaryX_map, RatFunc.algebraMap_X]
      exact hx.symm
    have hpy : algebraMap ℚ[X] RF (primaryY (Polynomial.X : ℚ[X]) j)=y := by
      rw [primaryY_map, RatFunc.algebraMap_X]
      exact hy.symm
    have hh : RationalFunctionFamily.curve.toAffine.Nonsingular
        (algebraMap ℚ[X] RF (primaryX (Polynomial.X : ℚ[X]) j))
        (algebraMap ℚ[X] RF (primaryY (Polynomial.X : ℚ[X]) j)) := by
      rw [hpx,hpy]
      exact h
    have he := hσ.polynomial_coordinates (primaryX (Polynomial.X : ℚ[X]) j)
      (primaryY (Polynomial.X : ℚ[X]) j) hh
    have hpoint : WeierstrassCurve.Affine.Point.some _ _ hh =
        WeierstrassCurve.Affine.Point.some x y h := by
      apply encode_injective
      simp only [encode,hpx,hpy]
    rw [hpoint] at he
    have hxe : (primaryX (Polynomial.X : ℚ[X]) j).eval r=primaryX r j := by
      simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_X] using
        primaryX_map (Polynomial.evalRingHom r) (Polynomial.X : ℚ[X]) j
    have hye : (primaryY (Polynomial.X : ℚ[X]) j).eval r=primaryY r j := by
      simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_X] using
        primaryY_map (Polynomial.evalRingHom r) (Polynomial.X : ℚ[X]) j
    simpa only [hxe,hye] using he

/-- The three specialized points as points on a smooth rational fiber. -/
def primaryPoints (r : ℚ) [(X r).IsElliptic] : Fin 3 → (X r).toAffine.Point :=
  ![point1 r,point2 r,point3 r]

theorem primaryPoints_coordinates (r : ℚ) [(X r).IsElliptic] (j : Fin 3) :
    encode (primaryPoints r j)=some (primaryX r j,primaryY r j) := by
  fin_cases j <;> rfl

/-- Equality of points, including the signs of all y-coordinates. -/
theorem CanonicalSpecializationAt.primary_points
    {r : ℚ} [(X r).IsElliptic]
    {σ : RationalFunctionFamily.curve.toAffine.Point →+ (X r).toAffine.Point}
    (hσ : CanonicalSpecializationAt _ _ r σ) (j : Fin 3) :
    σ (RationalFunctionFamily.points j) = primaryPoints r j := by
  apply encode_injective
  rw [hσ.primary_points_coordinates, primaryPoints_coordinates]

/-- At m=14/3 the specialization can be chosen injective and sends the
three generic sections to the three rational points. -/
theorem X_injective_specialization_14_with_points
    (hGT : GusicTadicTheorem11) [(X (14/3 : ℚ)).IsElliptic] :
    ∃ σ : RationalFunctionFamily.curve.toAffine.Point →+ (X (14/3 : ℚ)).toAffine.Point,
      Function.Injective σ ∧ ∀ j, σ (RationalFunctionFamily.points j)=primaryPoints (14/3) j := by
  obtain ⟨σ,hσ,hI⟩ := X_injective_specialization_14 hGT
  exact ⟨σ,hI,hσ.primary_points⟩

end
end Z2Z4Rank6.GusicTadic
