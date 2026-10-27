module

public import Common.Elliptic.WeierstrassSchemeCoefficientCharts

@[expose] public section

/-!
# Coefficient extension is a pushout on every cubic chart

The universal map is constructed by polynomial evaluation, passage to
the cubic quotient and the homogeneous localization.
-/
namespace WeierstrassScheme.CoefficientMap
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial GenericCharts
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] (f : k →+* K)
variable (W : WeierstrassCurve k) (i : Fin 3)
variable {S : Type} [CommRing S] (l : K →+* S) (r : ChartRing W i →+* S)
variable (hc : ∀ a : k,l (f a)=r (algebraMap k (ChartRing W i) a))

def pushoutEvaluation : CoordinateRing (W.map f) →+* S :=
  Ideal.Quotient.lift (definingIdeal (W.map f))
    (MvPolynomial.eval₂Hom l (fun j=>r (ratio W i j))) (by
      have hker : definingIdeal (W.map f) ≤
          RingHom.ker (MvPolynomial.eval₂Hom l (fun j=>r (ratio W i j))) := by
        apply Ideal.span_le.mpr
        rintro p (rfl : p=relation (W.map f))
        change MvPolynomial.eval₂Hom l (fun j=>r (ratio W i j)) (relation (W.map f))=0
        have h := congrArg r (ratio_relation W i)
        simp only [map_sub,map_add,map_mul,map_pow,map_zero] at h
        simpa only [relation,map_sub,map_add,map_mul,map_pow,MvPolynomial.eval₂Hom_X',
          MvPolynomial.eval₂Hom_C,WeierstrassCurve.map_a₁,WeierstrassCurve.map_a₂,
          WeierstrassCurve.map_a₃,WeierstrassCurve.map_a₄,WeierstrassCurve.map_a₆,hc] using h
      intro p hp
      exact hker hp)

@[simp] theorem pushoutEvaluation_coordinate (j : Fin 3) :
    pushoutEvaluation f W i l r hc (coordinate (W.map f) j)=r (ratio W i j) := by
  change MvPolynomial.eval₂Hom l (fun j=>r (ratio W i j)) (X j)=_
  simp

@[simp] theorem pushoutEvaluation_scalar (a : K) :
    pushoutEvaluation f W i l r hc (algebraMap K (CoordinateRing (W.map f)) a)=l a := by
  change MvPolynomial.eval₂Hom l (fun j=>r (ratio W i j)) (C a)=_
  simp

theorem pushoutEvaluation_normalized :
    pushoutEvaluation f W i l r hc (coordinate (W.map f) i)=1 := by
  simp [ratio_self]

def pushoutDesc : ChartRing (W.map f) i →+* S :=
  chartRingEvaluation (W.map f) i (pushoutEvaluation f W i l r hc)
    (pushoutEvaluation_normalized f W i l r hc)

@[simp] theorem pushoutDesc_ratio (j : Fin 3) :
    pushoutDesc f W i l r hc (ratio (W.map f) i j)=r (ratio W i j) := by
  simp [pushoutDesc]

@[simp] theorem pushoutDesc_scalar (a : K) :
    pushoutDesc f W i l r hc (algebraMap K (ChartRing (W.map f) i) a)=l a := by
  simp [pushoutDesc]

theorem chart_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap k (ChartRing W i)))
      (CommRingCat.ofHom f) (CommRingCat.ofHom (chartHom f W i))
      (CommRingCat.ofHom (algebraMap K (ChartRing (W.map f) i))) := by
  have hw : CommRingCat.ofHom (algebraMap k (ChartRing W i))≫
      CommRingCat.ofHom (chartHom f W i)=
      CommRingCat.ofHom f≫CommRingCat.ofHom (algebraMap K (ChartRing (W.map f) i)) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (chartHom_scalar f W i)
  apply IsPushout.of_isColimit' ⟨hw⟩
  have hc' (s : PushoutCocone (CommRingCat.ofHom (algebraMap k (ChartRing W i)))
      (CommRingCat.ofHom f)) (a : k) :
      s.inr.hom (f a)=s.inl.hom (algebraMap k (ChartRing W i) a) := by
    exact (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp s.condition) a).symm
  refine PushoutCocone.IsColimit.mk hw
    (fun s=>CommRingCat.ofHom (pushoutDesc f W i s.inr.hom s.inl.hom (hc' s))) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply chartRingHom_ext W i
    · intro a
      change pushoutDesc f W i s.inr.hom s.inl.hom (hc' s)
        (chartHom f W i (algebraMap k (ChartRing W i) a))=_
      rw [chartHom_scalar,pushoutDesc_scalar]
      exact hc' s a
    · intro j
      simp
  · intro s
    apply CommRingCat.hom_ext
    exact RingHom.ext (pushoutDesc_scalar f W i s.inr.hom s.inl.hom (hc' s))
  · intro s m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply chartRingHom_ext (W.map f) i
    · intro a
      have h := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hm₂) a
      simpa using h
    · intro j
      have h := RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hm₁) (ratio W i j)
      simpa using h

theorem chart_field_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (chartHom f W i)))
      (Spec.map (CommRingCat.ofHom (algebraMap K (ChartRing (W.map f) i))))
      (Spec.map (CommRingCat.ofHom (algebraMap k (ChartRing W i))))
      (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (chart_isPushout f W i)

end
end WeierstrassScheme.CoefficientMap
