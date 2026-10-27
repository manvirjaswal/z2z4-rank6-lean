import Z2Z4Rank6.BaseGeometry
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# The affine coordinate algebra and scheme of C

Jaswal, DOI 10.5281/zenodo.23437117, Lemma 4.1(a) and
Theorem 1.2(a). The coordinate order is (m,u,v). This file constructs
Q[M,U,V]/(U²−15M²−1210,V²−10M²−1215), its Spec and
structural morphism, and the unit-ideal certificate for the Jacobian minors.
Smoothness is proved in `AffineBaseSchemeSmooth`.
-/
namespace Z2Z4Rank6.AffineBaseScheme
noncomputable section
open scoped Classical
open CategoryTheory AlgebraicGeometry

abbrev P := MvPolynomial (Fin 3) ℚ

def relation (i : Fin 2) : P :=
  ![(MvPolynomial.X 1)^2-15*(MvPolynomial.X 0)^2-1210,
    (MvPolynomial.X 2)^2-10*(MvPolynomial.X 0)^2-1215] i

def definingIdeal : Ideal P := Ideal.span (Set.range relation)

abbrev CoordinateRing := P ⧸ definingIdeal

def m : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 0)
def u : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 1)
def v : CoordinateRing := Ideal.Quotient.mk definingIdeal (MvPolynomial.X 2)

/-- The finite quotient presentation. -/
def presentation : Algebra.Presentation ℚ CoordinateRing (Fin 3) (Fin 2) :=
  Algebra.Presentation.naive (v:=relation)

instance coordinateRing_finitePresentation : Algebra.FinitePresentation ℚ CoordinateRing :=
  presentation.finitePresentation_of_isFinite

@[simp] theorem relation_zero (i : Fin 2) :
    Ideal.Quotient.mk definingIdeal (relation i)=0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i,rfl⟩

theorem u_sq : u^2=15*m^2+1210 := by
  have h := relation_zero 0
  simp only [relation,Matrix.cons_val_zero,map_sub,map_pow,map_mul,map_ofNat] at h
  change u^2-15*m^2-1210=0 at h
  linear_combination h

theorem v_sq : v^2=10*m^2+1215 := by
  have h := relation_zero 1
  simp only [relation,Matrix.cons_val_one,Matrix.cons_val_zero,map_sub,map_pow,map_mul,map_ofNat] at h
  change v^2-10*m^2-1215=0 at h
  linear_combination h

/-- Evaluation at a rational C-point. -/
def evaluation (c : CPoint) : CoordinateRing →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ definingIdeal (MvPolynomial.aeval ![c.m,c.u,c.v]) (by
    have hker : definingIdeal≤RingHom.ker (MvPolynomial.aeval ![c.m,c.u,c.v]).toRingHom := by
      apply Ideal.span_le.mpr
      rintro p ⟨i,rfl⟩
      change (MvPolynomial.aeval ![c.m,c.u,c.v]) (relation i)=0
      fin_cases i <;> simp [relation] <;> nlinarith [c.u_sq,c.v_sq]
    intro p hp
    exact hker hp)

@[simp] theorem evaluation_m (c : CPoint) : evaluation c m=c.m := by
  change (MvPolynomial.aeval ![c.m,c.u,c.v]) (MvPolynomial.X 0)=c.m
  simp
@[simp] theorem evaluation_u (c : CPoint) : evaluation c u=c.u := by
  change (MvPolynomial.aeval ![c.m,c.u,c.v]) (MvPolynomial.X 1)=c.u
  simp
@[simp] theorem evaluation_v (c : CPoint) : evaluation c v=c.v := by
  change (MvPolynomial.aeval ![c.m,c.u,c.v]) (MvPolynomial.X 2)=c.v
  simp

instance coordinateRing_nontrivial : Nontrivial CoordinateRing := by
  refine ⟨⟨0,1,?_⟩⟩
  intro h
  have he := congrArg (evaluation baseC0) h
  simp at he

/-- The affine Q-scheme. -/
def scheme : Scheme := Spec (CommRingCat.of CoordinateRing)

def structureMap : scheme ⟶ Spec (CommRingCat.of ℚ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℚ CoordinateRing))

/-- Products corresponding to the three 2×2 Jacobian minors, up to rational units. -/
def minorFactor (i : Fin 3) : CoordinateRing := ![u*v,m*v,m*u] i

private theorem mem_of_unit_mul_mem {R : Type*} [CommRing R] (I : Ideal R)
    (a b : R) (ha : IsUnit a) (h : a*b∈I) : b∈I := by
  obtain ⟨a,rfl⟩ := ha
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using I.mul_mem_left (↑a⁻¹) h

/-- The minors cover Spec: their factors generate the unit ideal.
The certificate uses 3v²−2u²=1225 and the two defining equations. -/
theorem minorFactors_span_top : Ideal.span (Set.range minorFactor)=⊤ := by
  let J : Ideal CoordinateRing := Ideal.span (Set.range minorFactor)
  have huv : u*v∈J := Ideal.subset_span ⟨0,rfl⟩
  have hmv : m*v∈J := Ideal.subset_span ⟨1,rfl⟩
  have hmu : m*u∈J := Ideal.subset_span ⟨2,rfl⟩
  have hline : 3*((m*v)*(m*v))-2*((m*u)*(m*u))∈J :=
    J.sub_mem (J.mul_mem_left 3 (J.mul_mem_left (m*v) hmv))
      (J.mul_mem_left 2 (J.mul_mem_left (m*u) hmu))
  have he : 3*((m*v)*(m*v))-2*((m*u)*(m*u))=1225*m^2 := by
    calc
      _=m^2*(3*v^2-2*u^2) := by ring
      _=_ := by rw [u_sq,v_sq]; ring
  rw [he] at hline
  have h1225 : IsUnit (1225 : CoordinateRing) := by
    simpa only [map_ofNat] using (show IsUnit (1225:ℚ) by norm_num).map (algebraMap ℚ CoordinateRing)
  have hm2 : m^2∈J := mem_of_unit_mul_mem J _ _ h1225 hline
  have huv2 : u^2*v^2∈J := by
    convert J.mul_mem_left (u*v) huv using 1
    ring
  have hconst : (1470150 : CoordinateRing)∈J := by
    have h := J.sub_mem huv2 (J.mul_mem_left (150*m^2+30325) hm2)
    convert h using 1
    rw [u_sq,v_sq]
    ring
  apply J.eq_top_of_isUnit_mem hconst
  simpa only [map_ofNat] using (show IsUnit (1470150:ℚ) by norm_num).map (algebraMap ℚ CoordinateRing)

end
end Z2Z4Rank6.AffineBaseScheme
