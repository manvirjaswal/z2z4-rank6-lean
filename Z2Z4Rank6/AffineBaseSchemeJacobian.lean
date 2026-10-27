import Z2Z4Rank6.AffineBaseScheme
import Mathlib.RingTheory.Smooth.StandardSmooth

/-! Submersive presentations on the three Jacobian charts of C,
for Jaswal Lemma 4.1(a), DOI 10.5281/zenodo.23437117. -/
namespace Z2Z4Rank6.AffineBaseScheme
noncomputable section
open scoped Classical

/-- The three choices of two columns of the two-row Jacobian. -/
def columnMap (i : Fin 3) : Fin 2→Fin 3 := ![![1,2],![0,2],![0,1]] i

theorem columnMap_injective (i : Fin 3) : Function.Injective (columnMap i) := by
  intro a b h
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [columnMap] at h ⊢

def prePresentation (i : Fin 3) : Algebra.PreSubmersivePresentation ℚ CoordinateRing (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v:=relation) (columnMap i) (columnMap_injective i)

def minorCoefficient (i : Fin 3) : ℚ := ![4,-60,40] i

theorem minorCoefficient_ne_zero (i : Fin 3) : minorCoefficient i≠0 := by
  fin_cases i <;> norm_num [minorCoefficient]

private theorem relation_zero_C : relation 0=
    (MvPolynomial.X 1)^2-MvPolynomial.C (15:ℚ)*(MvPolynomial.X 0)^2-MvPolynomial.C (1210:ℚ) := by
  simp [relation,map_ofNat]

private theorem relation_one_C : relation 1=
    (MvPolynomial.X 2)^2-MvPolynomial.C (10:ℚ)*(MvPolynomial.X 0)^2-MvPolynomial.C (1215:ℚ) := by
  simp [relation,map_ofNat]

private theorem pderiv_relation_zero (j : Fin 3) :
    MvPolynomial.pderiv j (relation 0)=
      2*MvPolynomial.X 1*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 1-
        MvPolynomial.C (15:ℚ)*(2*MvPolynomial.X 0*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 0) := by
  rw [relation_zero_C]
  simp only [map_sub,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Nat.reduceSub,pow_one,sub_zero,Nat.cast_ofNat]

private theorem pderiv_relation_one (j : Fin 3) :
    MvPolynomial.pderiv j (relation 1)=
      2*MvPolynomial.X 2*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 2-
        MvPolynomial.C (10:ℚ)*(2*MvPolynomial.X 0*Pi.single (M:=fun _ : Fin 3 => P) j (1:P) 0) := by
  rw [relation_one_C]
  simp only [map_sub,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_C_mul,
    MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Nat.reduceSub,pow_one,sub_zero,Nat.cast_ofNat]

/-- Determinant computation in the quotient algebra. -/
theorem prePresentation_jacobian (i : Fin 3) :
    (prePresentation i).jacobian=algebraMap ℚ CoordinateRing (minorCoefficient i)*minorFactor i := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,Matrix.det_fin_two]
  simp only [-Matrix.cons_val,Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change Ideal.Quotient.mk definingIdeal
    (MvPolynomial.pderiv (columnMap i 0) (relation 0)*MvPolynomial.pderiv (columnMap i 1) (relation 1)-
      MvPolynomial.pderiv (columnMap i 0) (relation 1)*MvPolynomial.pderiv (columnMap i 1) (relation 0))=
    algebraMap ℚ CoordinateRing (minorCoefficient i)*minorFactor i
  simp only [-Matrix.cons_val,pderiv_relation_zero,pderiv_relation_one]
  fin_cases i <;>
    simp [-Matrix.cons_val,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,columnMap,minorCoefficient,minorFactor,m,u,v,map_ofNat] <;> ring

end
end Z2Z4Rank6.AffineBaseScheme
