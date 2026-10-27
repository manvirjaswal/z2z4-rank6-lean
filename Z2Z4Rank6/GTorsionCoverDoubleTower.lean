module

public import Z2Z4Rank6.DoubleSquareCover

@[expose] public section

/-! The polynomial normal-form algebra for two square roots.
All constructions work for arbitrary radicands. -/
namespace Z2Z4Rank6.DoubleSquareCover
noncomputable section
open Polynomial
abbrev First (f : Fin 2→Poly) := QuadraticAlgebra Poly (f 0) 0
def secondRadicand (f : Fin 2→Poly) : First f := algebraMap Poly (First f) (f 1)
abbrev Tower (f : Fin 2→Poly) := QuadraticAlgebra (First f) (secondRadicand f) 0

def towerParameter (f : Fin 2→Poly) : Tower f := algebraMap Poly (Tower f) Polynomial.X
def towerRoot (f : Fin 2→Poly) : Fin 2→Tower f :=
  ![algebraMap (First f) (Tower f) QuadraticAlgebra.omega,QuadraticAlgebra.omega]

private theorem omega_sq {R : Type*} [CommRing R] (a : R) :
    (QuadraticAlgebra.omega:QuadraticAlgebra R a 0)^2=algebraMap R (QuadraticAlgebra R a 0) a := by
  rw [sq,QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
  simp only [map_zero,zero_mul,add_zero]

theorem towerRoot_sq (f : Fin 2→Poly) (i : Fin 2) :
    (towerRoot f i)^2=algebraMap Poly (Tower f) (f i) := by
  fin_cases i
  · change (algebraMap (First f) (Tower f) (QuadraticAlgebra.omega:First f))^2=
      algebraMap Poly (Tower f) (f 0)
    rw [←map_pow,omega_sq]
    exact (IsScalarTower.algebraMap_apply Poly (First f) (Tower f) _).symm
  · change (QuadraticAlgebra.omega:Tower f)^2=algebraMap Poly (Tower f) (f 1)
    rw [omega_sq]
    exact (IsScalarTower.algebraMap_apply Poly (First f) (Tower f) _).symm

theorem polynomial_aeval_tower (f : Fin 2→Poly) (p : Poly) :
    Polynomial.aeval (towerParameter f) p=algebraMap Poly (Tower f) p := by
  have hh : (Polynomial.aeval (towerParameter f)).toRingHom=algebraMap Poly (Tower f) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change Polynomial.aeval (towerParameter f) Polynomial.X=towerParameter f
      exact Polynomial.aeval_X _
  exact RingHom.congr_fun hh p

def coordinateToTower (f : Fin 2→Poly) : CoordinateRing f→ₐ[ℚ]Tower f :=
  lift f (towerParameter f) (towerRoot f) (fun i=>by rw [polynomial_aeval_tower];exact towerRoot_sq f i)
@[simp] theorem coordinateToTower_parameter (f : Fin 2→Poly) :
    coordinateToTower f (parameter f)=towerParameter f := lift_parameter _ _ _ _
@[simp] theorem coordinateToTower_root (f : Fin 2→Poly) (i : Fin 2) :
    coordinateToTower f (root f i)=towerRoot f i := lift_root _ _ _ _ i

def polynomialToCoordinate (f : Fin 2→Poly) : Poly→+*CoordinateRing f :=
  (Polynomial.aeval (parameter f)).toRingHom
@[simp] theorem polynomialToCoordinate_X (f : Fin 2→Poly) :
    polynomialToCoordinate f Polynomial.X=parameter f := Polynomial.aeval_X _

theorem first_coordinate_root (f : Fin 2→Poly) :
    (root f 0)^2=polynomialToCoordinate f (f 0) := by
  change (root f 0)^2=Polynomial.aeval (parameter f) (f 0)
  exact root_sq f 0

def firstToCoordinate (f : Fin 2→Poly) : First f→+*CoordinateRing f :=
  quadraticRingLift (f 0) (polynomialToCoordinate f) (root f 0) (first_coordinate_root f)

theorem second_coordinate_root (f : Fin 2→Poly) :
    (root f 1)^2=firstToCoordinate f (secondRadicand f) := by
  rw [secondRadicand,firstToCoordinate,quadraticRingLift_algebraMap]
  exact root_sq f 1

def towerToCoordinateRing (f : Fin 2→Poly) : Tower f→+*CoordinateRing f :=
  quadraticRingLift (secondRadicand f) (firstToCoordinate f) (root f 1) (second_coordinate_root f)
def towerToCoordinate (f : Fin 2→Poly) : Tower f→ₐ[ℚ]CoordinateRing f where
  __ := towerToCoordinateRing f
  commutes' := (towerToCoordinateRing f).map_rat_algebraMap

@[simp] theorem towerToCoordinate_parameter (f : Fin 2→Poly) :
    towerToCoordinate f (towerParameter f)=parameter f := by
  change towerToCoordinateRing f (algebraMap Poly (Tower f) Polynomial.X)=_
  rw [IsScalarTower.algebraMap_apply Poly (First f) (Tower f)]
  simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,firstToCoordinate,polynomialToCoordinate_X]

@[simp] theorem towerToCoordinate_root (f : Fin 2→Poly) (i : Fin 2) :
    towerToCoordinate f (towerRoot f i)=root f i := by
  fin_cases i
  · change towerToCoordinateRing f (algebraMap (First f) (Tower f) QuadraticAlgebra.omega)=root f 0
    simp only [towerToCoordinateRing,quadraticRingLift_algebraMap,
      firstToCoordinate,quadraticRingLift_omega]
  · change towerToCoordinateRing f QuadraticAlgebra.omega=root f 1
    exact quadraticRingLift_omega _ _ _ _

theorem towerToCoordinate_comp (f : Fin 2→Poly) :
    (towerToCoordinate f).comp (coordinateToTower f)=AlgHom.id ℚ (CoordinateRing f) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun i=>?_) i
  · change towerToCoordinate f (coordinateToTower f (parameter f))=parameter f
    rw [coordinateToTower_parameter,towerToCoordinate_parameter]
  · change towerToCoordinate f (coordinateToTower f (root f i))=root f i
    rw [coordinateToTower_root,towerToCoordinate_root]

theorem coordinateToTower_injective (f : Fin 2→Poly) : Function.Injective (coordinateToTower f) := by
  apply Function.LeftInverse.injective (g:=towerToCoordinate f)
  intro z
  exact AlgHom.congr_fun (towerToCoordinate_comp f) z
end
end Z2Z4Rank6.DoubleSquareCover
