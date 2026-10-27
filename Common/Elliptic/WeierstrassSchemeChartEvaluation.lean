import Common.Elliptic.WeierstrassSchemeGenericCharts

/-! Universal normalized evaluations on Weierstrass charts. -/
namespace WeierstrassScheme.GenericCharts
noncomputable section
open MvPolynomial CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] (W : WeierstrassCurve F)

theorem scalar_val (i : Fin 3) (a : F) :
    (algebraMap F (ChartRing W i) a).val=
      algebraMap (CoordinateRing W) (LocalizedRing W i)
        (algebraMap F (CoordinateRing W) a) := by
  change Localization.mk (algebraMap F (CoordinateRing W) a)
    (1 : Submonoid.powers (coordinate W i))=_
  exact Localization.mk_one_eq_algebraMap _

variable {S : Type} [CommRing S]

theorem evaluationCoordinateUnit (i : Fin 3) (e : CoordinateRing W →+* S)
    (he : e (coordinate W i)=1) : IsUnit (e (coordinate W i)) := by
  rw [he]
  exact isUnit_one

def chartRingEvaluation (i : Fin 3) (e : CoordinateRing W →+* S)
    (he : e (coordinate W i)=1) : ChartRing W i →+* S :=
  (Localization.awayLift e (coordinate W i) (evaluationCoordinateUnit W i e he)).comp
    (algebraMap (ChartRing W i) (LocalizedRing W i))

@[simp] theorem chartRingEvaluation_ratio (i j : Fin 3) (e : CoordinateRing W →+* S)
    (he : e (coordinate W i)=1) :
    chartRingEvaluation W i e he (ratio W i j)=e (coordinate W j) := by
  change Localization.awayLift e (coordinate W i) (evaluationCoordinateUnit W i e he)
    (ratio W i j).val=_
  rw [ratio_val,map_mul,IsLocalization.Away.lift_eq]
  have hi : Localization.awayLift e (coordinate W i) (evaluationCoordinateUnit W i e he)
      (inverseCoordinate W i)=1 := by
    have h := congrArg (Localization.awayLift e (coordinate W i)
      (evaluationCoordinateUnit W i e he)) (coordinate_mul_inverse W i)
    simp only [map_mul,map_one,IsLocalization.Away.lift_eq] at h
    simpa only [he,one_mul] using h
  rw [hi,mul_one]

@[simp] theorem chartRingEvaluation_scalar (i : Fin 3) (e : CoordinateRing W →+* S)
    (he : e (coordinate W i)=1) (a : F) :
    chartRingEvaluation W i e he (algebraMap F (ChartRing W i) a)=
      e (algebraMap F (CoordinateRing W) a) := by
  change Localization.awayLift e (coordinate W i) (evaluationCoordinateUnit W i e he)
    (algebraMap F (ChartRing W i) a).val=_
  rw [scalar_val,IsLocalization.Away.lift_eq]

theorem chartRingHom_ext (i : Fin 3) (f g : ChartRing W i →+* S)
    (hs : ∀ a : F,f (algebraMap F (ChartRing W i) a)=g (algebraMap F (ChartRing W i) a))
    (hr : ∀ j,f (ratio W i j)=g (ratio W i j)) : f=g := by
  let : Algebra F S := (f.comp (algebraMap F (ChartRing W i))).toAlgebra
  let f' : ChartRing W i →ₐ[F] S := {toRingHom:=f,commutes':=fun _=>rfl}
  let g' : ChartRing W i →ₐ[F] S := {toRingHom:=g,commutes':=fun a=>(hs a).symm}
  exact congrArg AlgHom.toRingHom (chartAlgHom_ext W i f' g' hr)

end
end WeierstrassScheme.GenericCharts
