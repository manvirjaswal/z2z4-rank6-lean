module

public import Common.AlgebraicGeometry.ProjectiveLineCharts

@[expose] public section

/-! The degree-zero localization charts are polynomial rings. -/
namespace AlgebraicGeometry.ProjectiveLine.Charts
noncomputable section
open scoped Classical
open MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable (k : Type) [Field k]

theorem scalar_val (i : Fin 2) (a : k) :
    (algebraMap k (ChartRing k i) a).val=
      algebraMap (Ring k) (LocalizedRing k i) (C a) := by
  change (HomogeneousLocalization.fromZeroRingHom (grading k)
    (Submonoid.powers (coordinate k i)) (algebraMap k (grading k 0) a)).val=_
  change Localization.mk (C a) (1 : Submonoid.powers (coordinate k i))=
    algebraMap (Ring k) (LocalizedRing k i) (C a)
  exact Localization.mk_one_eq_algebraMap (C a)

variable {k} {S : Type} [CommRing S] [Algebra k S]

theorem evaluationCoordinateUnit (i : Fin 2) (e : Ring k →ₐ[k] S)
    (he : e (coordinate k i)=1) : IsUnit (e.toRingHom (coordinate k i)) := by
  change IsUnit (e (coordinate k i))
  rw [he]
  exact isUnit_one

def chartEvaluation (i : Fin 2) (e : Ring k →ₐ[k] S) (he : e (coordinate k i)=1) :
    ChartRing k i →ₐ[k] S where
  toRingHom := (Localization.awayLift e.toRingHom (coordinate k i)
    (evaluationCoordinateUnit i e he)).comp
      (algebraMap (ChartRing k i) (LocalizedRing k i))
  commutes' a := by
    change Localization.awayLift e.toRingHom (coordinate k i) (evaluationCoordinateUnit i e he)
      (algebraMap k (ChartRing k i) a).val=algebraMap k S a
    rw [scalar_val,IsLocalization.Away.lift_eq]
    exact e.commutes a

@[simp] theorem chartEvaluation_ratio (i j : Fin 2) (e : Ring k →ₐ[k] S)
    (he : e (coordinate k i)=1) : chartEvaluation i e he (ratio k i j)=e (coordinate k j) := by
  change Localization.awayLift e.toRingHom (coordinate k i) (evaluationCoordinateUnit i e he)
    (ratio k i j).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift e.toRingHom (coordinate k i) (evaluationCoordinateUnit i e he)
      (inverseCoordinate k i)=1 := by
    have h := congrArg (Localization.awayLift e.toRingHom (coordinate k i)
      (evaluationCoordinateUnit i e he)) (coordinate_mul_inverse k i)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    change e (coordinate k i)*Localization.awayLift e.toRingHom (coordinate k i) _ _=1 at h
    simpa only [he,one_mul] using h
  rw [hi,mul_one]
  rfl

variable (k)
def otherCoordinate : Fin 2 → Fin 2 := ![1,0]

def polynomialCoordinates (i : Fin 2) : Ring k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun j=>if j=i then 1 else Polynomial.X)

theorem polynomialCoordinates_normalized (i : Fin 2) :
    polynomialCoordinates k i (coordinate k i)=1 := by
  simp [polynomialCoordinates,coordinate]

def toPolynomial (i : Fin 2) : ChartRing k i →ₐ[k] Polynomial k :=
  chartEvaluation i (polynomialCoordinates k i) (polynomialCoordinates_normalized k i)

def fromPolynomial (i : Fin 2) : Polynomial k →ₐ[k] ChartRing k i :=
  Polynomial.aeval (ratio k i (otherCoordinate i))

@[simp] theorem toPolynomial_ratio (i j : Fin 2) :
    toPolynomial k i (ratio k i j)=(if j=i then 1 else Polynomial.X) := by
  simp [toPolynomial,polynomialCoordinates,coordinate]

def polynomialEquiv (i : Fin 2) : ChartRing k i ≃ₐ[k] Polynomial k :=
  AlgEquiv.ofAlgHom (toPolynomial k i) (fromPolynomial k i)
    (by
      apply Polynomial.algHom_ext
      fin_cases i <;> simp [fromPolynomial,otherCoordinate])
    (by
      apply chartAlgHom_ext k i
      intro j
      by_cases h : j = i
      · subst h
        simp
      · fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | simp [fromPolynomial,otherCoordinate])

end
end AlgebraicGeometry.ProjectiveLine.Charts
