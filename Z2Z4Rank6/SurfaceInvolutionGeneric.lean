module

public import Z2Z4Rank6.SurfaceInvolutionBase
public import Z2Z4Rank6.SurfaceRationalData

@[expose] public section

/-!
# The semilinear generic cubic involution

The map on the homogeneous cubic is
(n,X,Y,Z) ↦ (9801/n,(99/n)^4 X,(99/n)^6 Y,Z).
It is proved directly on the homogeneous quotient rings.
-/
namespace Z2Z4Rank6.SurfaceInvolution
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial WeierstrassScheme
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance rationalFunctionAlgebraGeneric : Algebra ℚ F := RatFunc.instAlgebraOfPolynomial ℚ ℚ

abbrev W := SurfaceRationalData.curve
abbrev n : F := RatFunc.X

theorem curve_a₁ : W.a₁=0 := by simp [W,SurfaceRationalData.curve,Common.Elliptic.SurfaceWeierstrassData.genericCurve,SurfaceRationalData.finiteEquation,SurfaceWeierstrassCharts.affineModel]
theorem curve_a₃ : W.a₃=0 := by simp [W,SurfaceRationalData.curve,Common.Elliptic.SurfaceWeierstrassData.genericCurve,SurfaceRationalData.finiteEquation,SurfaceWeierstrassCharts.affineModel]
theorem curve_a₆ : W.a₆=0 := by simp [W,SurfaceRationalData.curve,Common.Elliptic.SurfaceWeierstrassData.genericCurve,SurfaceRationalData.finiteEquation,SurfaceWeierstrassCharts.affineModel]

theorem curve_a₂ : W.a₂=surfaceS n := by
  simp [W,SurfaceRationalData.curve,Common.Elliptic.SurfaceWeierstrassData.genericCurve,
    SurfaceRationalData.finiteEquation,SurfaceWeierstrassCharts.affineModel,surfaceS,n]
  simp only [map_ofNat]

theorem curve_a₄ : W.a₄=(surfaceW n)^2 := by
  simp [W,SurfaceRationalData.curve,Common.Elliptic.SurfaceWeierstrassData.genericCurve,
    SurfaceRationalData.finiteEquation,SurfaceWeierstrassCharts.affineModel,surfaceW,n]
  simp only [map_ofNat]

def ratio : F := 99/n

theorem reciprocal_ratio : reciprocalFieldMap ratio=ratio⁻¹ := by
  simp only [ratio,map_div₀,map_ofNat,reciprocalFieldMap_X]
  field_simp
  ring

theorem reciprocal_a₂ : reciprocalFieldMap W.a₂=ratio^4*W.a₂ := by
  rw [curve_a₂]
  have ht : reciprocalFieldMap (surfaceS n)=surfaceS (9801/n) := by
    simp only [surfaceS,map_mul,map_add,map_sub,map_pow,map_ofNat,reciprocalFieldMap_X]
  rw [ht,surfaceS_involution n RatFunc.X_ne_zero]
  rfl

theorem reciprocal_a₄ : reciprocalFieldMap W.a₄=ratio^8*W.a₄ := by
  rw [curve_a₄,map_pow]
  have ht : reciprocalFieldMap (surfaceW n)=surfaceW (9801/n) := by
    simp only [surfaceW,map_mul,map_neg,map_sub,map_ofNat,map_one,reciprocalFieldMap_X]
  rw [ht,surfaceW_involution n RatFunc.X_ne_zero]
  dsimp only [ratio]
  ring

def cubicCoordinates : Fin 3 → PolynomialRing F :=
  ![C (ratio^4)*MvPolynomial.X 0,C (ratio^6)*MvPolynomial.X 1,MvPolynomial.X 2]

@[simp] theorem cubicCoordinates_zero : cubicCoordinates 0=C (ratio^4)*MvPolynomial.X 0 := rfl
@[simp] theorem cubicCoordinates_one : cubicCoordinates 1=C (ratio^6)*MvPolynomial.X 1 := rfl
@[simp] theorem cubicCoordinates_two : cubicCoordinates 2=MvPolynomial.X 2 := rfl

def cubicSubstitution : PolynomialRing F →+* PolynomialRing F :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp reciprocalFieldMap.toRingHom) cubicCoordinates

@[simp] theorem cubicSubstitution_C (a : F) :
    cubicSubstitution (C a)=C (reciprocalFieldMap a) := by
  simp [cubicSubstitution]

@[simp] theorem cubicSubstitution_X (i : Fin 3) :
    cubicSubstitution (MvPolynomial.X i)=cubicCoordinates i := by
  simp [cubicSubstitution]

theorem cubicCoordinates_homogeneous (i : Fin 3) : (cubicCoordinates i).IsHomogeneous 1 := by
  fin_cases i
  · change (C (ratio^4)*MvPolynomial.X (0 : Fin 3)).IsHomogeneous 1
    exact (isHomogeneous_X F (0 : Fin 3)).C_mul (ratio^4)
  · change (C (ratio^6)*MvPolynomial.X (1 : Fin 3)).IsHomogeneous 1
    exact (isHomogeneous_X F (1 : Fin 3)).C_mul (ratio^6)
  · change (MvPolynomial.X (2 : Fin 3)).IsHomogeneous 1
    exact isHomogeneous_X F (2 : Fin 3)

theorem cubicSubstitution_homogeneous {p : PolynomialRing F} {d : ℕ}
    (hp : p.IsHomogeneous d) : (cubicSubstitution p).IsHomogeneous d := by
  change (MvPolynomial.eval₂ _ cubicCoordinates p).IsHomogeneous d
  simpa only [one_mul] using hp.eval₂ _ cubicCoordinates
    (fun a=>isHomogeneous_C (Fin 3) (reciprocalFieldMap a)) cubicCoordinates_homogeneous

theorem cubicSubstitution_square : cubicSubstitution.comp cubicSubstitution=RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change cubicSubstitution (cubicSubstitution (C a))=C a
    simp only [cubicSubstitution_C]
    exact congrArg C (DFunLike.congr_fun reciprocalFieldMap_square a)
  · intro i
    change cubicSubstitution (cubicSubstitution (MvPolynomial.X i))=MvPolynomial.X i
    rw [cubicSubstitution_X]
    have hr : ratio≠0 := div_ne_zero (by norm_num) RatFunc.X_ne_zero
    fin_cases i
    · change cubicSubstitution (C (ratio^4)*MvPolynomial.X 0)=MvPolynomial.X 0
      rw [map_mul,cubicSubstitution_C,map_pow,reciprocal_ratio,cubicSubstitution_X,
        cubicCoordinates_zero,←mul_assoc,←C_mul]
      simp [hr]
    · change cubicSubstitution (C (ratio^6)*MvPolynomial.X 1)=MvPolynomial.X 1
      rw [map_mul,cubicSubstitution_C,map_pow,reciprocal_ratio,cubicSubstitution_X,
        cubicCoordinates_one,←mul_assoc,←C_mul]
      simp [hr]
    · change cubicSubstitution (MvPolynomial.X 2)=MvPolynomial.X 2
      exact cubicSubstitution_X 2


theorem cubicSubstitution_relation :
    cubicSubstitution (relation W)=C (ratio^12)*relation W := by
  simp only [relation,map_sub,map_add,map_mul,map_pow,cubicSubstitution_X,cubicSubstitution_C,
    curve_a₁,curve_a₃,curve_a₆,map_zero,cubicCoordinates_zero,cubicCoordinates_one,
    cubicCoordinates_two,reciprocal_a₂,reciprocal_a₄]
  simp only [zero_mul,add_zero,sub_zero]
  ring


def cubicQuotientMap : CoordinateRing W →+* CoordinateRing W :=
  Ideal.Quotient.lift (definingIdeal W)
    ((Ideal.Quotient.mk (definingIdeal W)).comp cubicSubstitution) (by
      have hker : definingIdeal W ≤ RingHom.ker
          ((Ideal.Quotient.mk (definingIdeal W)).comp cubicSubstitution) := by
        apply Ideal.span_le.mpr
        rintro p (rfl : p=relation W)
        change Ideal.Quotient.mk _ (cubicSubstitution (relation W))=0
        rw [cubicSubstitution_relation,map_mul]
        have hz : Ideal.Quotient.mk (definingIdeal W) (relation W)=0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
        rw [hz,mul_zero]
      intro p hp
      exact hker hp)

@[simp] theorem cubicQuotientMap_mk (p : PolynomialRing F) :
    cubicQuotientMap (Ideal.Quotient.mk (definingIdeal W) p)=
      Ideal.Quotient.mk (definingIdeal W) (cubicSubstitution p) := rfl

def cubicGraded : grading W →+*ᵍ grading W where
  toRingHom := cubicQuotientMap
  map_mem := by
    intro d p hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact ⟨cubicSubstitution q,cubicSubstitution_homogeneous hq,rfl⟩

theorem cubicGraded_square : cubicGraded.comp cubicGraded=GradedRingHom.id (grading W) := by
  apply GradedRingHom.ext
  intro p
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective p
  change cubicQuotientMap (cubicQuotientMap (Ideal.Quotient.mk (definingIdeal W) q))=_
  rw [cubicQuotientMap_mk,cubicQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (definingIdeal W))
    (DFunLike.congr_fun cubicSubstitution_square q)

def genericInvolution : scheme W ≅ scheme W :=
  Proj.isoOfInverse cubicGraded cubicGraded cubicGraded_square cubicGraded_square

theorem genericInvolution_over : genericInvolution.hom≫structureMap W=
    structureMap W≫genericBaseInvolution.hom := by
  have hc : CommRingCat.ofHom (algebraMap F (grading W 0))≫
      CommRingCat.ofHom cubicGraded.gradedZeroRingHom=
      CommRingCat.ofHom reciprocalFieldMap.toRingHom≫
        CommRingCat.ofHom (algebraMap F (grading W 0)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply Subtype.ext
    change cubicQuotientMap (Ideal.Quotient.mk _ (C a))=
      Ideal.Quotient.mk _ (C (reciprocalFieldMap a))
    rw [cubicQuotientMap_mk,cubicSubstitution_C]
  change Proj.map cubicGraded _≫(Proj.toSpecZero _≫
      Spec.map (CommRingCat.ofHom (algebraMap F (grading W 0))))=
    (Proj.toSpecZero _≫Spec.map (CommRingCat.ofHom (algebraMap F (grading W 0))))≫_
  rw [←Category.assoc,Proj.map_toSpecZero,Category.assoc,←Spec.map_comp,hc,
    Spec.map_comp,Category.assoc]
  rfl

end
end Z2Z4Rank6.SurfaceInvolution
