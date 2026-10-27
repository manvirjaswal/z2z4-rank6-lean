module

public import Z2Z4Rank6.ECProjectiveSchemeInfinity
public import Z2Z4Rank6.ECProjectiveInfinityPolynomial

@[expose] public section

/-!
# The infinity-chart algebra as a monic cubic extension

Jaswal, DOI 10.5281/zenodo.23437117, Theorem 1.2(a), Lemma 4.1.
The quotient Q[x,z]/(z−x³−x²z+137620xz²+10504000z³)
is identified by inverse universal maps with AdjoinRoot of the displayed
monic Eisenstein cubic over Q[z].
-/
namespace Z2Z4Rank6.ECProjectiveInfinityCoordinate
noncomputable section
open Polynomial
open ECProjectiveInfinityPolynomial

abbrev CoordinateRing := ECProjectiveSchemeInfinity.CoordinateRing

def towerX : Tower := AdjoinRoot.root cubic
def towerZ : Tower := algebraMap Poly Tower Polynomial.X

theorem tower_equation :
    towerZ=towerX^3+towerX^2*towerZ-137620*towerX*towerZ^2-10504000*towerZ^3 := by
  have h : Polynomial.aeval towerX cubic=0 := by
    change Polynomial.aeval (AdjoinRoot.root cubic) cubic=0
    rw [AdjoinRoot.aeval_eq,AdjoinRoot.mk_self]
  simp only [cubic,map_add,map_sub,map_mul,map_pow,aeval_X,aeval_C] at h
  simp only [map_ofNat] at h
  change towerX^3+towerZ*towerX^2-137620*towerZ^2*towerX-
    (10504000*towerZ^3+towerZ)=0 at h
  linear_combination -h

def coordinateToTower : CoordinateRing →ₐ[ℚ] Tower :=
  Ideal.Quotient.liftₐ ECProjectiveSchemeInfinity.definingIdeal
    (MvPolynomial.aeval ![towerX,towerZ]) (by
      have hker : ECProjectiveSchemeInfinity.definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![towerX,towerZ]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval ![towerX,towerZ]) (ECProjectiveSchemeInfinity.relation i)=0
        simp only [ECProjectiveSchemeInfinity.relation,map_add,map_sub,map_mul,map_pow,map_ofNat,
          MvPolynomial.aeval_X,Matrix.cons_val_zero,Matrix.cons_val_one]
        linear_combination tower_equation
      intro p hp
      exact hker hp)

@[simp] theorem coordinateToTower_x :
    coordinateToTower ECProjectiveSchemeInfinity.x=towerX := by
  change (MvPolynomial.aeval ![towerX,towerZ]) (MvPolynomial.X 0)=towerX
  simp
@[simp] theorem coordinateToTower_z :
    coordinateToTower ECProjectiveSchemeInfinity.z=towerZ := by
  change (MvPolynomial.aeval ![towerX,towerZ]) (MvPolynomial.X 1)=towerZ
  simp

def polynomialToCoordinate : Poly →+* CoordinateRing :=
  (Polynomial.aeval ECProjectiveSchemeInfinity.z).toRingHom

@[simp] theorem polynomialToCoordinate_X :
    polynomialToCoordinate Polynomial.X=ECProjectiveSchemeInfinity.z := by
  change (Polynomial.aeval ECProjectiveSchemeInfinity.z) Polynomial.X=_
  exact Polynomial.aeval_X _

theorem coordinate_root :
    cubic.eval₂ polynomialToCoordinate ECProjectiveSchemeInfinity.x=0 := by
  simp only [cubic,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,
    map_add,map_mul,map_pow,map_ofNat,polynomialToCoordinate_X]
  norm_num
  linear_combination -ECProjectiveSchemeInfinity.equation

def towerToCoordinateRing : Tower →+* CoordinateRing :=
  AdjoinRoot.lift polynomialToCoordinate ECProjectiveSchemeInfinity.x coordinate_root

def towerToCoordinate : Tower →ₐ[ℚ] CoordinateRing where
  __ := towerToCoordinateRing
  commutes' := towerToCoordinateRing.map_rat_algebraMap

@[simp] theorem towerToCoordinate_x : towerToCoordinate towerX=ECProjectiveSchemeInfinity.x :=
  AdjoinRoot.lift_root coordinate_root
@[simp] theorem towerToCoordinate_z : towerToCoordinate towerZ=ECProjectiveSchemeInfinity.z := by
  change towerToCoordinateRing (AdjoinRoot.of cubic Polynomial.X)=_
  rw [towerToCoordinateRing,AdjoinRoot.lift_of,polynomialToCoordinate_X]

theorem towerToCoordinate_comp :
    towerToCoordinate.comp coordinateToTower=AlgHom.id ℚ CoordinateRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change towerToCoordinate (coordinateToTower ECProjectiveSchemeInfinity.x)=ECProjectiveSchemeInfinity.x
    rw [coordinateToTower_x,towerToCoordinate_x]
  · change towerToCoordinate (coordinateToTower ECProjectiveSchemeInfinity.z)=ECProjectiveSchemeInfinity.z
    rw [coordinateToTower_z,towerToCoordinate_z]

theorem coordinateToTower_injective : Function.Injective coordinateToTower := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate)
  intro x
  exact AlgHom.congr_fun towerToCoordinate_comp x

/-- The Y-chart ring is a domain, by its proved cubic normal form. -/
instance infinityCoordinateRingIsDomain : IsDomain CoordinateRing :=
  coordinateToTower_injective.isDomain coordinateToTower

theorem coordinateToTower_polynomial (p : Poly) :
    coordinateToTower (polynomialToCoordinate p)=algebraMap Poly Tower p := by
  have h : coordinateToTower.toRingHom.comp polynomialToCoordinate=algebraMap Poly Tower := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change coordinateToTower (polynomialToCoordinate Polynomial.X)=towerZ
      rw [polynomialToCoordinate_X,coordinateToTower_z]
  exact RingHom.congr_fun h p

theorem towerToCoordinate_polynomial (p : Poly) :
    towerToCoordinate (algebraMap Poly Tower p)=polynomialToCoordinate p :=
  AdjoinRoot.lift_of coordinate_root

theorem coordinateToTower_comp :
    coordinateToTower.comp towerToCoordinate=AlgHom.id ℚ Tower := by
  apply AlgHom.coe_ringHom_injective
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro p
    change coordinateToTower (towerToCoordinate (algebraMap Poly Tower p))=algebraMap Poly Tower p
    rw [towerToCoordinate_polynomial,coordinateToTower_polynomial]
  · change coordinateToTower (towerToCoordinate towerX)=towerX
    rw [towerToCoordinate_x,coordinateToTower_x]

def coordinateTowerEquiv : CoordinateRing ≃ₐ[ℚ] Tower :=
  {coordinateToTower with
    invFun:=towerToCoordinate
    left_inv:=fun x=>AlgHom.congr_fun towerToCoordinate_comp x
    right_inv:=fun x=>AlgHom.congr_fun coordinateToTower_comp x}

instance infinityPolynomialAlgebra : Algebra Poly CoordinateRing := polynomialToCoordinate.toAlgebra

def coordinateTowerPolynomialEquiv : CoordinateRing ≃ₐ[Poly] Tower where
  __ := coordinateTowerEquiv.toRingEquiv
  commutes' := coordinateToTower_polynomial

/-- The Y-chart is finite over Q[z]. -/
instance infinityModuleFinite : Module.Finite Poly CoordinateRing :=
  Module.Finite.equiv coordinateTowerPolynomialEquiv.symm.toLinearEquiv

end
end Z2Z4Rank6.ECProjectiveInfinityCoordinate
