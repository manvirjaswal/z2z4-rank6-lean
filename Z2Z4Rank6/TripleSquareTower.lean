module

public import Z2Z4Rank6.TripleSquareCover

@[expose] public section

/-! The polynomial normal-form algebra for three square roots.
All constructions work for arbitrary radicands. -/
namespace Z2Z4Rank6.TripleSquareCover
noncomputable section
open Polynomial
abbrev First (f : Fin 3→Poly) := QuadraticAlgebra Poly (f 0) 0
def secondRadicand (f : Fin 3→Poly) : First f := algebraMap Poly (First f) (f 1)
abbrev Second (f : Fin 3→Poly) := QuadraticAlgebra (First f) (secondRadicand f) 0
def thirdRadicand (f : Fin 3→Poly) : Second f := algebraMap Poly (Second f) (f 2)
abbrev Tower (f : Fin 3→Poly) := QuadraticAlgebra (Second f) (thirdRadicand f) 0

def towerParameter (f : Fin 3→Poly) : Tower f := algebraMap Poly (Tower f) Polynomial.X
def towerRoot (f : Fin 3→Poly) : Fin 3→Tower f :=
  ![algebraMap (First f) (Tower f) QuadraticAlgebra.omega,
    algebraMap (Second f) (Tower f) QuadraticAlgebra.omega,QuadraticAlgebra.omega]

private theorem omega_sq {R : Type*} [CommRing R] (a : R) :
    (QuadraticAlgebra.omega:QuadraticAlgebra R a 0)^2=algebraMap R (QuadraticAlgebra R a 0) a := by
  rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero]

theorem towerRoot_sq (f : Fin 3→Poly) (i : Fin 3) :
    (towerRoot f i)^2=algebraMap Poly (Tower f) (f i) := by
  fin_cases i
  · change (algebraMap (First f) (Tower f) (QuadraticAlgebra.omega:First f))^2=
      algebraMap Poly (Tower f) (f 0)
    rw [←map_pow,omega_sq]
    exact (IsScalarTower.algebraMap_apply Poly (First f) (Tower f) _).symm
  · change (algebraMap (Second f) (Tower f) (QuadraticAlgebra.omega:Second f))^2=
      algebraMap Poly (Tower f) (f 1)
    rw [←map_pow,omega_sq]
    change algebraMap (Second f) (Tower f) (algebraMap (First f) (Second f)
      (algebraMap Poly (First f) (f 1)))=_
    rw [←IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f),
      ←IsScalarTower.algebraMap_apply Poly (First f) (Tower f)]
  · change (QuadraticAlgebra.omega:Tower f)^2=algebraMap Poly (Tower f) (f 2)
    rw [omega_sq]
    exact (IsScalarTower.algebraMap_apply Poly (Second f) (Tower f) _).symm

theorem polynomial_aeval_tower (f : Fin 3→Poly) (p : Poly) :
    Polynomial.aeval (towerParameter f) p=algebraMap Poly (Tower f) p := by
  have hh : (Polynomial.aeval (towerParameter f)).toRingHom=algebraMap Poly (Tower f) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change Polynomial.aeval (towerParameter f) Polynomial.X=towerParameter f
      exact Polynomial.aeval_X _
  exact RingHom.congr_fun hh p

def coordinateToTower (f : Fin 3→Poly) : CoordinateRing f→ₐ[ℚ]Tower f :=
  lift f (towerParameter f) (towerRoot f) (fun i=>by rw [polynomial_aeval_tower];exact towerRoot_sq f i)
@[simp] theorem coordinateToTower_parameter (f : Fin 3→Poly) :
    coordinateToTower f (parameter f)=towerParameter f := lift_parameter _ _ _ _
@[simp] theorem coordinateToTower_root (f : Fin 3→Poly) (i : Fin 3) :
    coordinateToTower f (root f i)=towerRoot f i := lift_root _ _ _ _ i

def polynomialToCoordinate (f : Fin 3→Poly) : Poly→+*CoordinateRing f :=
  (Polynomial.aeval (parameter f)).toRingHom
@[simp] theorem polynomialToCoordinate_X (f : Fin 3→Poly) :
    polynomialToCoordinate f Polynomial.X=parameter f := Polynomial.aeval_X _

theorem first_coordinate_root (f : Fin 3→Poly) :
    (root f 0)^2=polynomialToCoordinate f (f 0) := by
  change (root f 0)^2=Polynomial.aeval (parameter f) (f 0)
  exact root_sq f 0

def firstToCoordinate (f : Fin 3→Poly) : First f→+*CoordinateRing f :=
  quadraticRingLift (f 0) (polynomialToCoordinate f) (root f 0) (first_coordinate_root f)

theorem second_coordinate_root (f : Fin 3→Poly) :
    (root f 1)^2=firstToCoordinate f (secondRadicand f) := by
  rw [secondRadicand,firstToCoordinate,quadraticRingLift_algebraMap]
  exact root_sq f 1

def secondToCoordinate (f : Fin 3→Poly) : Second f→+*CoordinateRing f :=
  quadraticRingLift (secondRadicand f) (firstToCoordinate f) (root f 1) (second_coordinate_root f)

theorem secondToCoordinate_polynomial (f : Fin 3→Poly) (p : Poly) :
    secondToCoordinate f (algebraMap Poly (Second f) p)=polynomialToCoordinate f p := by
  rw [IsScalarTower.algebraMap_apply Poly (First f) (Second f)]
  simp only [secondToCoordinate,quadraticRingLift_algebraMap,firstToCoordinate]

theorem third_coordinate_root (f : Fin 3→Poly) :
    (root f 2)^2=secondToCoordinate f (thirdRadicand f) := by
  rw [thirdRadicand,secondToCoordinate_polynomial]
  exact root_sq f 2

def towerToCoordinateRing (f : Fin 3→Poly) : Tower f→+*CoordinateRing f :=
  quadraticRingLift (thirdRadicand f) (secondToCoordinate f) (root f 2) (third_coordinate_root f)
def towerToCoordinate (f : Fin 3→Poly) : Tower f→ₐ[ℚ]CoordinateRing f where
  __ := towerToCoordinateRing f
  commutes' := (towerToCoordinateRing f).map_rat_algebraMap

@[simp] theorem towerToCoordinate_parameter (f : Fin 3→Poly) :
    towerToCoordinate f (towerParameter f)=parameter f := by
  change towerToCoordinateRing f (algebraMap Poly (Tower f) Polynomial.X)=_
  rw [IsScalarTower.algebraMap_apply Poly (Second f) (Tower f)]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,
    secondToCoordinate_polynomial,polynomialToCoordinate_X]

@[simp] theorem towerToCoordinate_root (f : Fin 3→Poly) (i : Fin 3) :
    towerToCoordinate f (towerRoot f i)=root f i := by
  fin_cases i
  · change towerToCoordinateRing f (algebraMap (First f) (Tower f) QuadraticAlgebra.omega)=root f 0
    rw [IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f)]
    simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,secondToCoordinate,
      firstToCoordinate,quadraticRingLift_omega]
  · change towerToCoordinateRing f (algebraMap (Second f) (Tower f) QuadraticAlgebra.omega)=root f 1
    simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,secondToCoordinate,quadraticRingLift_omega]
  · change towerToCoordinateRing f QuadraticAlgebra.omega=root f 2
    exact quadraticRingLift_omega _ _ _ _

theorem towerToCoordinate_comp (f : Fin 3→Poly) :
    (towerToCoordinate f).comp (coordinateToTower f)=AlgHom.id ℚ (CoordinateRing f) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun i=>?_) i
  · change towerToCoordinate f (coordinateToTower f (parameter f))=parameter f
    rw [coordinateToTower_parameter,towerToCoordinate_parameter]
  · change towerToCoordinate f (coordinateToTower f (root f i))=root f i
    rw [coordinateToTower_root,towerToCoordinate_root]

theorem coordinateToTower_injective (f : Fin 3→Poly) : Function.Injective (coordinateToTower f) := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate f)
  intro z
  exact AlgHom.congr_fun (towerToCoordinate_comp f) z
end
end Z2Z4Rank6.TripleSquareCover
