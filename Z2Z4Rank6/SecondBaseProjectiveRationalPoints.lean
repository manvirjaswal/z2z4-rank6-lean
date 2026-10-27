import Z2Z4Rank6.SecondBaseProjectiveScheme
import Z2Z4Rank6.SecondQuarticG2

/-!
# Printed second-base points as projective scheme points

Every solution of the three printed G2 equations gives a morphism
Spec Q to the projective intersection, over Spec Q. The map is injective,
so the established infinitude of printed points proves infinitude for this
projective scheme as well.
-/

namespace Z2Z4Rank6.SecondBaseProjectiveRationalPoints
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
open SecondBaseProjectiveScheme
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Source := Spec (CommRingCat.of ℚ)
abbrev ChartRing := HomogeneousLocalization.Away grading z
abbrev LocalizedRing := Localization.Away z

instance chartAlgebra : Algebra ℚ ChartRing :=
  ((HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers z)).comp
    (algebraMap ℚ (grading 0))).toAlgebra

theorem scaled_s2_sq (P : SecondFamily.G2Point ℚ) :
    (1089*P.s2)^2=34391709*P.s1^2-751709 := by
  have h := P.s2_sq
  rw [SecondFamily.qA,SecondFamily.beta] at h
  rw [P.s1_sq]
  norm_num at h
  linear_combination 1185921*h

theorem scaled_s3_sq (P : SecondFamily.G2Point ℚ) :
    (1089*P.s3)^2= -751709*P.s1^2+3779309 := by
  have h := P.s3_sq
  rw [SecondFamily.qB,SecondFamily.beta,SecondFamily.gamma] at h
  rw [P.s1_sq]
  norm_num at h
  linear_combination 1185921*h

def homogeneousEvaluation (P : SecondFamily.G2Point ℚ) : CoordinateRing →ₐ[ℚ] ℚ :=
  Ideal.Quotient.liftₐ definingIdeal
    (MvPolynomial.aeval ![P.s1,1089*P.s2,1089*P.s3,1]) (by
      have hker : definingIdeal≤RingHom.ker
          (MvPolynomial.aeval ![P.s1,1089*P.s2,1089*P.s3,1]).toRingHom := by
        apply Ideal.span_le.mpr
        rintro p ⟨i,rfl⟩
        change (MvPolynomial.aeval _) (relation i)=0
        fin_cases i
        · norm_num [relation,model]
          linear_combination scaled_s2_sq P
        · norm_num [relation,model]
          linear_combination scaled_s3_sq P
      intro p hp
      exact hker hp)

@[simp] theorem homogeneousEvaluation_coordinate (P : SecondFamily.G2Point ℚ) (i : Fin 4) :
    homogeneousEvaluation P (coordinate i)=![P.s1,1089*P.s2,1089*P.s3,1] i := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  simp

def ratio (i : Fin 4) : ChartRing :=
  HomogeneousLocalization.Away.mk grading (coordinate_degree 3) 1 (coordinate i)
    (by simpa using coordinate_degree i)

def inverseZ : LocalizedRing := IsLocalization.Away.invSelf z

theorem z_mul_inverseZ : algebraMap CoordinateRing LocalizedRing z*inverseZ=1 :=
  IsLocalization.Away.mul_invSelf _

theorem ratio_val (i : Fin 4) :
    (ratio i).val=algebraMap CoordinateRing LocalizedRing (coordinate i)*inverseZ := by
  simp only [ratio,HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk',IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one,inverseZ,IsLocalization.Away.invSelf]

def chartEvaluation (P : SecondFamily.G2Point ℚ) : ChartRing →+* ℚ :=
  (Localization.awayLift (homogeneousEvaluation P).toRingHom z (by simp [z])).comp
    (algebraMap ChartRing LocalizedRing)

@[simp] theorem chartEvaluation_ratio (P : SecondFamily.G2Point ℚ) (i : Fin 4) :
    chartEvaluation P (ratio i)=![P.s1,1089*P.s2,1089*P.s3,1] i := by
  change Localization.awayLift (homogeneousEvaluation P).toRingHom z (by simp [z])
    (ratio i).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hz : Localization.awayLift (homogeneousEvaluation P).toRingHom z (by simp [z]) inverseZ=1 := by
    have he := congrArg (Localization.awayLift (homogeneousEvaluation P).toRingHom z
      (by simp [z])) z_mul_inverseZ
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at he
    change homogeneousEvaluation P z * _=1 at he
    simpa [z] using he
  rw [hz,mul_one]
  exact homogeneousEvaluation_coordinate P i

def chartInclusion : Spec (CommRingCat.of ChartRing) ⟶ scheme :=
  Proj.awayι grading z (coordinate_degree 3) (by decide : 0<1)

instance chartInclusion_openImmersion : IsOpenImmersion chartInclusion := by
  dsimp only [chartInclusion]
  infer_instance

def pointMorphism (P : SecondFamily.G2Point ℚ) : Source ⟶ scheme :=
  Spec.map (CommRingCat.ofHom (chartEvaluation P)) ≫ chartInclusion

theorem pointMorphism_injective : Function.Injective pointMorphism := by
  intro P Q h
  have hs := (cancel_mono chartInclusion).mp h
  have he := Spec.map_injective hs
  have hm := congrArg (fun f : CommRingCat.of ChartRing ⟶ CommRingCat.of ℚ => f (ratio 0)) he
  have hu := congrArg (fun f : CommRingCat.of ChartRing ⟶ CommRingCat.of ℚ => f (ratio 1)) he
  have hv := congrArg (fun f : CommRingCat.of ChartRing ⟶ CommRingCat.of ℚ => f (ratio 2)) he
  change chartEvaluation P (ratio 0)=chartEvaluation Q (ratio 0) at hm
  change chartEvaluation P (ratio 1)=chartEvaluation Q (ratio 1) at hu
  change chartEvaluation P (ratio 2)=chartEvaluation Q (ratio 2) at hv
  rw [chartEvaluation_ratio,chartEvaluation_ratio] at hm hu hv
  change P.s1=Q.s1 at hm
  change 1089*P.s2=1089*Q.s2 at hu
  change 1089*P.s3=1089*Q.s3 at hv
  apply SecondFamily.G2Point.ext
  · rw [←P.s1_sq,←Q.s1_sq,hm]
  · exact hm
  · linarith
  · linarith

theorem chartInclusion_structureMap : chartInclusion ≫ structureMap=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ChartRing)) := by
  dsimp only [chartInclusion,structureMap,QuadricIntersectionModel.structureMap,
    scheme,QuadricIntersectionModel.scheme]
  rw [←Category.assoc,Proj.awayι_toSpecZero,←Spec.map_comp]
  rfl

theorem pointMorphism_over (P : SecondFamily.G2Point ℚ) :
    pointMorphism P ≫ structureMap=𝟙 Source := by
  rw [pointMorphism,Category.assoc,chartInclusion_structureMap,←Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap ℚ ChartRing) ≫
      CommRingCat.ofHom (chartEvaluation P)=𝟙 (CommRingCat.of ℚ) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext_rat _ _
  rw [he,Spec.map_id]

abbrev RationalPoint := {p : Source ⟶ scheme // p ≫ structureMap=𝟙 Source}

def fromPrinted (P : SecondFamily.G2Point ℚ) : RationalPoint :=
  ⟨pointMorphism P,pointMorphism_over P⟩

theorem fromPrinted_injective : Function.Injective fromPrinted := by
  intro P Q h
  exact pointMorphism_injective (congrArg Subtype.val h)

/-- The printed point with theta=10/3 has W=s1=1. -/
def printedBasePoint : SecondFamily.G2Point ℚ where
  W := 1
  s1 := 1
  s2 := 5800/1089
  s3 := 580/363
  s1_sq := by norm_num
  s2_sq := by norm_num [SecondFamily.qA,SecondFamily.beta]
  s3_sq := by norm_num [SecondFamily.qB,SecondFamily.beta,SecondFamily.gamma]

def basePoint : RationalPoint := fromPrinted printedBasePoint

theorem rationalPoint_nonempty : Nonempty RationalPoint := ⟨basePoint⟩

theorem rationalPoints_infinite (hOdd : OddPrimeTorsionIntegrality) : Infinite RationalPoint := by
  let : Infinite (SecondFamily.G2Point ℚ) := secondG2_infinite hOdd
  exact Infinite.of_injective fromPrinted fromPrinted_injective

end
end Z2Z4Rank6.SecondBaseProjectiveRationalPoints
