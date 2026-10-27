import Z2Z4Rank6.AffineBaseLaurentBasis
import Z2Z4Rank6.InfinityBaseNormalForm

/-! The infinity-chart restriction into the affine overlap:
Z↦m⁻¹,U↦u/m,V↦v/m. The inverse of m is constructed from its localization unit. -/
namespace Z2Z4Rank6.AffineBaseFunctionFieldIso
noncomputable section

theorem overlapDenominators_eq : overlapDenominators=Submonoid.powers AffineBaseScheme.m := by
  change (Submonoid.powers (Polynomial.X:Poly)).map (algebraMap Poly CoordinateRing)=_
  rw [Submonoid.map_powers]
  congr 1
  exact polynomialToCoordinate_X

instance affineOverlapAwayM : IsLocalization.Away AffineBaseScheme.m OverlapRing := by
  change IsLocalization (Submonoid.powers AffineBaseScheme.m) OverlapRing
  rw [←overlapDenominators_eq]
  infer_instance

def mDenominator : overlapDenominators := ⟨AffineBaseScheme.m,by
  change ∃p∈Submonoid.powers (Polynomial.X:Poly),algebraMap Poly CoordinateRing p=AffineBaseScheme.m
  refine ⟨Polynomial.X,⟨1,pow_one _⟩,?_⟩
  exact polynomialToCoordinate_X⟩

def overlapMUnit : OverlapRingˣ := (IsLocalization.map_units OverlapRing mDenominator).unit
@[simp] theorem overlapMUnit_val : (overlapMUnit:OverlapRing)=
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.m :=
  (IsLocalization.map_units OverlapRing mDenominator).unit_spec

def inverseM : OverlapRing := ↑overlapMUnit⁻¹

theorem m_mul_inverseM : algebraMap CoordinateRing OverlapRing AffineBaseScheme.m*inverseM=1 := by
  rw [←overlapMUnit_val]
  exact Units.mul_inv _
theorem inverseM_mul_m : inverseM*algebraMap CoordinateRing OverlapRing AffineBaseScheme.m=1 := by
  rw [←overlapMUnit_val]
  exact Units.inv_mul _

theorem scalarLaurent_T_one : algebraMap Laurent OverlapRing (LaurentPolynomial.T 1)=
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.m := by
  calc
    _=algebraMap Laurent OverlapRing (algebraMap Poly Laurent Polynomial.X) := by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent,Polynomial.toLaurent_X]
    _=algebraMap Poly OverlapRing Polynomial.X :=
      (IsScalarTower.algebraMap_apply Poly Laurent OverlapRing _).symm
    _=algebraMap CoordinateRing OverlapRing (algebraMap Poly CoordinateRing Polynomial.X) :=
      IsScalarTower.algebraMap_apply Poly CoordinateRing OverlapRing _
    _=_ := by rw [show algebraMap Poly CoordinateRing Polynomial.X=AffineBaseScheme.m from polynomialToCoordinate_X]

theorem scalarLaurent_T_neg_one : algebraMap Laurent OverlapRing (LaurentPolynomial.T (-1))=inverseM := by
  have hp : algebraMap Laurent OverlapRing (LaurentPolynomial.T 1)*
      algebraMap Laurent OverlapRing (LaurentPolynomial.T (-1))=1 := by
    rw [←map_mul,←LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  rw [scalarLaurent_T_one] at hp
  have hh := congrArg (fun z : OverlapRing=>inverseM*z) hp
  simpa only [←mul_assoc,inverseM_mul_m,one_mul,mul_one] using hh

private theorem scaled_square {R : Type*} [CommRing R] (m u z a b : R)
    (hu : u^2=a*m^2+b) (hm : m*z=1) : (u*z)^2=b*z^2+a := by
  calc
    _=u^2*z^2 := by ring
    _=(a*m^2+b)*z^2 := by rw [hu]
    _=b*z^2+a*(m*z)^2 := by ring
    _=b*z^2+a := by rw [hm,one_pow,mul_one]

theorem overlap_u_scaled :
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM)^2=1210*inverseM^2+15 := by
  have hu := congrArg (algebraMap CoordinateRing OverlapRing) AffineBaseScheme.u_sq
  simp only [map_pow,map_add,map_mul,map_ofNat] at hu
  exact scaled_square (R:=OverlapRing)
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.m)
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.u) inverseM 15 1210 hu m_mul_inverseM

theorem overlap_v_scaled :
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM)^2=1215*inverseM^2+10 := by
  have hv := congrArg (algebraMap CoordinateRing OverlapRing) AffineBaseScheme.v_sq
  simp only [map_pow,map_add,map_mul,map_ofNat] at hv
  exact scaled_square (R:=OverlapRing)
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.m)
    (algebraMap CoordinateRing OverlapRing AffineBaseScheme.v) inverseM 10 1215 hv m_mul_inverseM

/-- The ring restriction obtained by the change of affine chart. -/
def infinityRestriction : ProjectiveBaseSchemeCharts.InfinityCoordinateRing→ₐ[ℚ]OverlapRing :=
  Ideal.Quotient.liftₐ ProjectiveBaseSchemeCharts.infinityIdeal
    (MvPolynomial.aeval ![inverseM,
      algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
      algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM]) (by
      have hker : ProjectiveBaseSchemeCharts.infinityIdeal≤RingHom.ker
          (MvPolynomial.aeval ![inverseM,
            algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
            algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval ![inverseM,
          algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
          algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM])
            (ProjectiveBaseSchemeCharts.infinityRelation i)=0
        fin_cases i <;> simp [ProjectiveBaseSchemeCharts.infinityRelation,overlap_u_scaled,overlap_v_scaled]
      intro p hp
      exact hker hp)

@[simp] theorem infinityRestriction_z : infinityRestriction ProjectiveBaseSchemeCharts.infinityZ=inverseM := by
  change (MvPolynomial.aeval ![inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM]) (MvPolynomial.X 0)=_
  simp
@[simp] theorem infinityRestriction_u : infinityRestriction ProjectiveBaseSchemeCharts.infinityU=
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM := by
  change (MvPolynomial.aeval ![inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM]) (MvPolynomial.X 1)=_
  simp
@[simp] theorem infinityRestriction_v : infinityRestriction ProjectiveBaseSchemeCharts.infinityV=
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM := by
  change (MvPolynomial.aeval ![inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.u*inverseM,
    algebraMap CoordinateRing OverlapRing AffineBaseScheme.v*inverseM]) (MvPolynomial.X 2)=_
  simp
end
end Z2Z4Rank6.AffineBaseFunctionFieldIso
