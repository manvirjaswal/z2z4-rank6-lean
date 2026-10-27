module

public import Z2Z4Rank6.TripleSquareTower
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Free eight-coefficient normal forms, in order 1,u,v,uv,r,ur,vr,uvr.
The coordinate quotient and polynomial quadratic tower are inverse algebras. -/
namespace Z2Z4Rank6.TripleSquareCover
noncomputable section
open Polynomial

private theorem quadraticRingHom_ext {R S : Type*} [CommRing R] [CommRing S]
    {a : R} (f g : QuadraticAlgebra R a 0→+*S)
    (hcoeff : ∀r,f (algebraMap R (QuadraticAlgebra R a 0) r)=g (algebraMap R (QuadraticAlgebra R a 0) r))
    (hroot : f QuadraticAlgebra.omega=g QuadraticAlgebra.omega) : f=g := by
  apply RingHom.ext
  intro z
  have hz : z=algebraMap R (QuadraticAlgebra R a 0) z.re+
      algebraMap R (QuadraticAlgebra R a 0) z.im*QuadraticAlgebra.omega := by
    simpa only [Algebra.smul_def,mul_one] using (QuadraticAlgebra.re_smul_add_im_smul z).symm
  rw [hz,map_add,map_add,map_mul,map_mul,hcoeff,hcoeff,hroot]

theorem coordinateToTower_polynomial (f : Fin 3→Poly) (p : Poly) :
    coordinateToTower f (polynomialToCoordinate f p)=algebraMap Poly (Tower f) p := by
  have hh : (coordinateToTower f).toRingHom.comp (polynomialToCoordinate f)=algebraMap Poly (Tower f) := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change coordinateToTower f (polynomialToCoordinate f Polynomial.X)=towerParameter f
      rw [polynomialToCoordinate_X,coordinateToTower_parameter]
  exact RingHom.congr_fun hh p

theorem coordinateToTower_comp (f : Fin 3→Poly) :
    (coordinateToTower f).comp (towerToCoordinate f)=AlgHom.id ℚ (Tower f) := by
  have hfirst : (coordinateToTower f).toRingHom.comp (firstToCoordinate f)=algebraMap (First f) (Tower f) := by
    apply quadraticRingHom_ext
    · intro p
      change coordinateToTower f (firstToCoordinate f (algebraMap Poly (First f) p))=_
      rw [firstToCoordinate,quadraticRingLift_algebraMap,coordinateToTower_polynomial]
      exact IsScalarTower.algebraMap_apply Poly (First f) (Tower f) p
    · change coordinateToTower f (firstToCoordinate f QuadraticAlgebra.omega)=_
      rw [firstToCoordinate,quadraticRingLift_omega,coordinateToTower_root]
      rfl
  have hsecond : (coordinateToTower f).toRingHom.comp (secondToCoordinate f)=algebraMap (Second f) (Tower f) := by
    apply quadraticRingHom_ext
    · intro p
      change coordinateToTower f (secondToCoordinate f (algebraMap (First f) (Second f) p))=_
      rw [secondToCoordinate,quadraticRingLift_algebraMap]
      exact (RingHom.congr_fun hfirst p).trans (IsScalarTower.algebraMap_apply (First f) (Second f) (Tower f) p)
    · change coordinateToTower f (secondToCoordinate f QuadraticAlgebra.omega)=_
      rw [secondToCoordinate,quadraticRingLift_omega,coordinateToTower_root]
      rfl
  have hthird : (coordinateToTower f).toRingHom.comp (towerToCoordinateRing f)=RingHom.id (Tower f) := by
    apply quadraticRingHom_ext
    · intro p
      change coordinateToTower f (towerToCoordinateRing f (algebraMap (Second f) (Tower f) p))=_
      rw [towerToCoordinateRing,quadraticRingLift_algebraMap]
      exact RingHom.congr_fun hsecond p
    · change coordinateToTower f (towerToCoordinateRing f QuadraticAlgebra.omega)=_
      rw [towerToCoordinateRing,quadraticRingLift_omega,coordinateToTower_root]
      rfl
  exact AlgHom.ext (RingHom.congr_fun hthird)

theorem coordinateToTower_surjective (f : Fin 3→Poly) : Function.Surjective (coordinateToTower f) := by
  intro z
  exact ⟨towerToCoordinate f z,AlgHom.congr_fun (coordinateToTower_comp f) z⟩

def coordinateTowerEquiv (f : Fin 3→Poly) : CoordinateRing f≃ₐ[ℚ]Tower f :=
  AlgEquiv.ofBijective (coordinateToTower f) ⟨coordinateToTower_injective f,coordinateToTower_surjective f⟩
instance coordinatePolynomialAlgebra (f : Fin 3→Poly) : Algebra Poly (CoordinateRing f) :=
  (polynomialToCoordinate f).toAlgebra

def coordinateTowerPolynomialEquiv (f : Fin 3→Poly) : CoordinateRing f≃ₐ[Poly]Tower f where
  __ := (coordinateTowerEquiv f).toRingEquiv
  commutes' := coordinateToTower_polynomial f

def basisIndexFour : Fin 4≃Fin 2×Fin 2 :=
  (finProdFinEquiv:Fin 2×Fin 2≃Fin 4).symm.trans (Equiv.prodComm _ _)
def basisIndex : Fin 8≃(Fin 2×Fin 2)×Fin 2 :=
  (finProdFinEquiv:Fin 2×Fin 4≃Fin 8).symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2)) basisIndexFour).trans (Equiv.prodComm _ _))

def twoBasis (f : Fin 3→Poly) : Module.Basis (Fin 2×Fin 2) Poly (Second f) :=
  (QuadraticAlgebra.basis (f 0) 0).smulTower (QuadraticAlgebra.basis (secondRadicand f) 0)
def towerBasis (f : Fin 3→Poly) : Module.Basis (Fin 8) Poly (Tower f) :=
  ((twoBasis f).smulTower (QuadraticAlgebra.basis (thirdRadicand f) 0)).reindex basisIndex.symm

def coordinateBasis (f : Fin 3→Poly) : Module.Basis (Fin 8) Poly (CoordinateRing f) :=
  (towerBasis f).map (coordinateTowerPolynomialEquiv f).symm.toLinearEquiv

@[simp] theorem coordinateTowerPolynomialEquiv_apply (f : Fin 3→Poly) (z : CoordinateRing f) :
    coordinateTowerPolynomialEquiv f z=coordinateToTower f z := rfl

theorem coordinateBasis_image (f : Fin 3→Poly) (i : Fin 8) :
    coordinateTowerPolynomialEquiv f (coordinateBasis f i)=towerBasis f i := by
  change coordinateTowerPolynomialEquiv f ((coordinateTowerPolynomialEquiv f).symm (towerBasis f i))=_
  exact (coordinateTowerPolynomialEquiv f).apply_symm_apply _

instance coordinateRing_moduleFinite (f : Fin 3→Poly) : Module.Finite Poly (CoordinateRing f) :=
  Module.Finite.of_basis (coordinateBasis f)
instance coordinateRing_nontrivial (f : Fin 3→Poly) : Nontrivial (CoordinateRing f) :=
  (coordinateToTower f).toRingHom.domain_nontrivial
end
end Z2Z4Rank6.TripleSquareCover
