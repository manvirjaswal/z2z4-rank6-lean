import Z2Z4Rank6.AffineBaseFunctionFieldIso
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Logic.Equiv.Fin.Basic

/-! Polynomial normal forms for the affine coordinate ring, in order
1,u,v,uv. Both universal-map compositions are proved, so this is a basis of
the quotient ring itself, not of a surrogate presentation. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
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

theorem coordinateToTower_polynomial (p : Poly) :
    coordinateToTower (polynomialToCoordinate p)=algebraMap Poly Tower p := by
  have hh : coordinateToTower.toRingHom.comp polynomialToCoordinate=algebraMap Poly Tower := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change coordinateToTower (polynomialToCoordinate Polynomial.X)=towerM
      rw [polynomialToCoordinate_X,coordinateToTower_m]
  exact RingHom.congr_fun hh p

theorem coordinateToTower_comp : coordinateToTower.comp towerToCoordinate=AlgHom.id ℚ Tower := by
  have hfirst : coordinateToTower.toRingHom.comp firstToCoordinate=algebraMap First Tower := by
    apply quadraticRingHom_ext
    · intro r
      change coordinateToTower (firstToCoordinate (algebraMap Poly First r))=
        algebraMap First Tower (algebraMap Poly First r)
      rw [firstToCoordinate,quadraticRingLift_algebraMap,coordinateToTower_polynomial]
      exact IsScalarTower.algebraMap_apply Poly First Tower r
    · change coordinateToTower (firstToCoordinate QuadraticAlgebra.omega)=towerU
      rw [firstToCoordinate,quadraticRingLift_omega,coordinateToTower_u]
  have hsecond : coordinateToTower.toRingHom.comp towerToCoordinateRing=RingHom.id Tower := by
    apply quadraticRingHom_ext
    · intro r
      change coordinateToTower (towerToCoordinateRing (algebraMap First Tower r))=algebraMap First Tower r
      rw [towerToCoordinateRing,quadraticRingLift_algebraMap]
      exact RingHom.congr_fun hfirst r
    · change coordinateToTower (towerToCoordinateRing QuadraticAlgebra.omega)=towerV
      rw [towerToCoordinateRing,quadraticRingLift_omega,coordinateToTower_v]
  exact AlgHom.ext (RingHom.congr_fun hsecond)

theorem coordinateToTower_surjective : Function.Surjective coordinateToTower := by
  intro z
  refine ⟨towerToCoordinate z,?_⟩
  exact AlgHom.congr_fun coordinateToTower_comp z

def coordinateTowerEquiv : CoordinateRing ≃ₐ[ℚ] Tower :=
  AlgEquiv.ofBijective coordinateToTower ⟨coordinateToTower_injective,coordinateToTower_surjective⟩

/-- The Q[M]-algebra structure, with M sent to the quotient coordinate m. -/
instance affineBaseCoordinatePolynomialAlgebra : Algebra Poly CoordinateRing := polynomialToCoordinate.toAlgebra

def coordinateTowerPolynomialEquiv : CoordinateRing ≃ₐ[Poly] Tower where
  __ := coordinateTowerEquiv.toRingEquiv
  commutes' := coordinateToTower_polynomial

/-- Product index order is changed explicitly from 1,v,u,uv to 1,u,v,uv. -/
def basisIndex : Fin 4 ≃ Fin 2 × Fin 2 :=
  (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm.trans (Equiv.prodComm _ _)

def towerBasis : Module.Basis (Fin 4) Poly Tower :=
  (((QuadraticAlgebra.basis firstRadicand 0).smulTower
    (QuadraticAlgebra.basis secondRadicandFirst 0)).reindex basisIndex.symm)

def coordinateBasis : Module.Basis (Fin 4) Poly CoordinateRing :=
  towerBasis.map coordinateTowerPolynomialEquiv.symm.toLinearEquiv

@[simp] theorem basisIndex_zero : basisIndex 0=(0,0) := rfl
@[simp] theorem basisIndex_one : basisIndex 1=(1,0) := rfl
@[simp] theorem basisIndex_two : basisIndex 2=(0,1) := rfl
@[simp] theorem basisIndex_three : basisIndex 3=(1,1) := rfl

theorem towerBasis_zero : towerBasis 0=1 := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_zero,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_zero,one_smul]
theorem towerBasis_one : towerBasis 1=towerU := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_one,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_zero,
    QuadraticAlgebra.basis_apply_one,Algebra.smul_def,mul_one,towerU]
theorem towerBasis_two : towerBasis 2=towerV := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_two,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_zero,
    QuadraticAlgebra.basis_apply_one,one_smul,towerV]
theorem towerBasis_three : towerBasis 3=towerU*towerV := by
  simp only [towerBasis,Module.Basis.reindex_apply,Equiv.symm_symm,basisIndex_three,
    Module.Basis.smulTower_apply,QuadraticAlgebra.basis_apply_one,
    Algebra.smul_def,towerU,towerV]

@[simp] theorem coordinateTowerPolynomialEquiv_apply (z : CoordinateRing) :
    coordinateTowerPolynomialEquiv z=coordinateToTower z := rfl

theorem coordinateBasis_image (i : Fin 4) :
    coordinateTowerPolynomialEquiv (coordinateBasis i)=towerBasis i := by
  change coordinateTowerPolynomialEquiv (coordinateTowerPolynomialEquiv.symm (towerBasis i))=towerBasis i
  exact coordinateTowerPolynomialEquiv.apply_symm_apply _

theorem coordinateBasis_zero : coordinateBasis 0=1 := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,towerBasis_zero,map_one]
theorem coordinateBasis_one : coordinateBasis 1=AffineBaseScheme.u := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,towerBasis_one,coordinateTowerPolynomialEquiv_apply,coordinateToTower_u]
theorem coordinateBasis_two : coordinateBasis 2=AffineBaseScheme.v := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,towerBasis_two,coordinateTowerPolynomialEquiv_apply,coordinateToTower_v]
theorem coordinateBasis_three : coordinateBasis 3=AffineBaseScheme.u*AffineBaseScheme.v := by
  apply coordinateTowerPolynomialEquiv.injective
  rw [coordinateBasis_image,towerBasis_three,map_mul,coordinateTowerPolynomialEquiv_apply,
    coordinateTowerPolynomialEquiv_apply,coordinateToTower_u,coordinateToTower_v]
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
