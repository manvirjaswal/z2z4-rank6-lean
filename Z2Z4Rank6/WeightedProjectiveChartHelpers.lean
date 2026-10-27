module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
# Degree-one affine charts in a positively weighted projective spectrum

Homogeneous fractions a/f^n, generation of the degree-zero
localization by weighted coordinate ratios, and the exact transition
identity. These generic proved helpers are used for weighted covers.
-/
namespace Z2Z4Rank6.WeightedProjectiveChartHelpers
noncomputable section
open scoped Classical BigOperators

variable {A : Type*} [CommRing A] [Algebra ℚ A]
variable (𝒜 : ℕ → Submodule ℚ A) [GradedAlgebra 𝒜]
variable {f : A} (hf : f∈𝒜 1)

abbrev Chart := HomogeneousLocalization.Away 𝒜 f
abbrev Localized := Localization.Away f

def fraction (n : ℕ) (a : A) (ha : a∈𝒜 n) : Chart 𝒜 (f:=f) :=
  HomogeneousLocalization.Away.mk 𝒜 hf n a (by simpa using ha)

def inverseCoordinate : Localized (f:=f) := IsLocalization.Away.invSelf f

omit [Algebra ℚ A] in
theorem coordinate_mul_inverse : algebraMap A (Localized (f:=f)) f*inverseCoordinate (f:=f)=1 :=
  IsLocalization.Away.mul_invSelf _

theorem fraction_val (n : ℕ) (a : A) (ha : a∈𝒜 n) :
    (fraction 𝒜 hf n a ha).val=algebraMap A (Localized (f:=f)) a*inverseCoordinate (f:=f)^n := by
  rw [fraction,HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  simp only [inverseCoordinate,IsLocalization.Away.invSelf,←IsLocalization.mk'_pow,one_pow]
  rfl

theorem fraction_self : fraction 𝒜 hf 1 f hf=1 := by
  apply HomogeneousLocalization.val_injective
  rw [fraction_val,HomogeneousLocalization.val_one,pow_one,coordinate_mul_inverse]

variable {ι : Type*} [Fintype ι]
variable (c : ι→A) (w : ι→ℕ) (hc : ∀i,c i∈𝒜 (w i))

theorem monomial_fraction (a : ℕ) (ai : ι→ℕ) (hai : ∑i,ai i*w i=a)
    (ha : (∏i,c i^ai i)∈𝒜 (a • (1:ℕ))) :
    HomogeneousLocalization.Away.mk 𝒜 hf a (∏i,c i^ai i) ha=
      ∏i,fraction 𝒜 hf (w i) (c i) (hc i)^ai i := by
  apply HomogeneousLocalization.val_injective
  calc
    _=algebraMap A (Localized (f:=f)) (∏i,c i^ai i)*inverseCoordinate (f:=f)^a := by
      rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',
        IsLocalization.mk'_eq_mul_mk'_one]
      congr 1
      simp only [inverseCoordinate,IsLocalization.Away.invSelf,←IsLocalization.mk'_pow,one_pow]
      rfl
    _=_ := by
      change _=algebraMap (Chart 𝒜 (f:=f)) (Localized (f:=f))
        (∏i,fraction 𝒜 hf (w i) (c i) (hc i)^ai i)
      rw [map_prod,map_prod]
      simp only [map_pow,HomogeneousLocalization.algebraMap_apply,fraction_val,mul_pow,←pow_mul]
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
      have he : ∑i,w i*ai i=a := by simpa only [mul_comm] using hai
      rw [he]

/-- Weighted coordinate ratios determine every ring map from the chart. -/
theorem ringHom_ext {S : Type*} [CommRing S]
    (hgen : Algebra.adjoin (𝒜 0) (Set.range c)=⊤)
    (hzero : ∀r : 𝒜 0,∃q : ℚ,r=algebraMap ℚ (𝒜 0) q)
    (F G : Chart 𝒜 (f:=f) →+* S)
    (h : ∀i,F (fraction 𝒜 hf (w i) (c i) (hc i))=
      G (fraction 𝒜 hf (w i) (c i) (hc i))) : F=G := by
  have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf c hgen w hc
  apply RingHom.ext
  intro x
  have hx : x∈Submodule.span (𝒜 0)
      {HomogeneousLocalization.Away.mk 𝒜 hf a (∏i,c i^ai i)
        (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ (fun i _ => hc i)) |
        (a : ℕ)(ai : ι→ℕ)(hai : ∑i,ai i • w i=a • (1:ℕ))} := by
    rw [hspan]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a,ai,hai,rfl⟩ := hy
    rw [monomial_fraction 𝒜 hf c w hc a ai (by simpa using hai)]
    simp only [map_prod,map_pow,h]
  | zero => simp
  | add x y hx hy hfx hfy => simp only [map_add,hfx,hfy]
  | smul r x hx hfx =>
    obtain ⟨q,rfl⟩ := hzero r
    change F (algebraMap (𝒜 0) (Chart 𝒜 (f:=f)) (algebraMap ℚ (𝒜 0) q)*x)=
      G (algebraMap (𝒜 0) (Chart 𝒜 (f:=f)) (algebraMap ℚ (𝒜 0) q)*x)
    have hq : F (algebraMap (𝒜 0) (Chart 𝒜 (f:=f)) (algebraMap ℚ (𝒜 0) q))=
        G (algebraMap (𝒜 0) (Chart 𝒜 (f:=f)) (algebraMap ℚ (𝒜 0) q)) :=
      RingHom.congr_fun (RingHom.ext_rat
        (F.comp ((algebraMap (𝒜 0) (Chart 𝒜 (f:=f))).comp (algebraMap ℚ (𝒜 0))))
        (G.comp ((algebraMap (𝒜 0) (Chart 𝒜 (f:=f))).comp (algebraMap ℚ (𝒜 0))))) q
    rw [map_mul,map_mul,hq,hfx]

end
end Z2Z4Rank6.WeightedProjectiveChartHelpers
