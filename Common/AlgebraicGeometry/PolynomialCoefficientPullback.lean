module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Monomial

@[expose] public section

/-! The affine-line coefficient square is cartesian. -/
namespace AlgebraicGeometry.PolynomialCoefficientPullback
noncomputable section
open CategoryTheory CategoryTheory.Limits Polynomial
variable (k K : Type) [CommRing k] [CommRing K] [Algebra k K]

theorem polynomial_isPushout :
    IsPushout (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))
      (CommRingCat.ofHom (algebraMap k K))
      (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K)))
      (CommRingCat.ofHom (Polynomial.C : K →+* K[X])) := by
  have hw : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K))=
      CommRingCat.ofHom (algebraMap k K) ≫
        CommRingCat.ofHom (Polynomial.C : K →+* K[X]) := by
    ext a
    simp
  apply IsPushout.of_isColimit' ⟨hw⟩
  refine PushoutCocone.IsColimit.mk hw
    (fun s=>CommRingCat.ofHom
      (Polynomial.eval₂RingHom s.inr.hom (s.inl.hom Polynomial.X))) ?_ ?_ ?_
  · intro s
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      have h := CommRingCat.hom_ext_iff.mp s.condition
      have ha := RingHom.congr_fun h a
      simpa using ha.symm
    · simp
  · intro s
    ext a
    simp
  · intro s m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      have h := CommRingCat.hom_ext_iff.mp hm₂
      simpa using RingHom.congr_fun h a
    · have h := CommRingCat.hom_ext_iff.mp hm₁
      simpa using RingHom.congr_fun h Polynomial.X

theorem affineLine_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* K[X])))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X])))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_isPushout k K)

end
end AlgebraicGeometry.PolynomialCoefficientPullback
