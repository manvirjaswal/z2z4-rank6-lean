import Z2Z4Rank6.LaurentCechQuotient
import Z2Z4Rank6.PositiveLaurentRange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Laurent chart coordinates for the genus-five third-twist base

The basis 1,u,v,uv,w,uw,vw,uvw has pole weights 0,1,1,2,1,2,2,3.
The two coefficient ranges leave the five displayed coefficients.
This module proves coefficient algebra; structure-sheaf maps and
cohomology are connected in the later chart and sheaf modules.
-/

namespace Z2Z4Rank6.ThirdTwistCoverLaurent
noncomputable section
open scoped Classical

abbrev Index := Fin 8 × ℤ
abbrev Coefficients := Index →₀ ℚ
abbrev EightLaurent := Fin 8 → LaurentPolynomial ℚ

def weights : Fin 8 → ℤ := ![0,1,1,2,1,2,2,3]
def positiveIndices : Set Index := {p | 0 ≤ p.2}
def negativeIndices : Set Index := {p | p.2 ≤ -weights p.1}

/-- The missing coefficients, in basis order and decreasing exponent. -/
def missingIndex : Fin 5 → Index :=
  ![(3,-1),(5,-1),(6,-1),(7,-1),(7,-2)]

theorem missingIndex_injective : Function.Injective missingIndex := by decide +kernel

def coordinatesEquiv : Coefficients ≃ₗ[ℚ] EightLaurent :=
  ((Finsupp.curryLinearEquiv ℚ).trans
    (Finsupp.linearEquivFunOnFinite ℚ (ℤ →₀ ℚ) (Fin 8))).trans
      (LinearEquiv.piCongrRight fun _ : Fin 8 =>
        (AddMonoidAlgebra.coeffLinearEquiv ℚ : LaurentPolynomial ℚ ≃ₗ[ℚ] (ℤ →₀ ℚ)).symm)

@[simp] theorem coordinatesEquiv_coeff (f : Coefficients) (i : Fin 8) (n : ℤ) :
    (coordinatesEquiv f i).coeff n = f (i,n) := rfl

def positivePart : Submodule ℚ Coefficients := Finsupp.supported ℚ ℚ positiveIndices
def negativePart : Submodule ℚ Coefficients := Finsupp.supported ℚ ℚ negativeIndices
def boundary : Submodule ℚ Coefficients := positivePart ⊔ negativePart

theorem positivePart_eq_span : positivePart =
    Submodule.span ℚ ((fun p : Index => Finsupp.single p (1 : ℚ)) '' positiveIndices) :=
  Finsupp.supported_eq_span_single ℚ positiveIndices

theorem negativePart_eq_span : negativePart =
    Submodule.span ℚ ((fun p : Index => Finsupp.single p (1 : ℚ)) '' negativeIndices) :=
  Finsupp.supported_eq_span_single ℚ negativeIndices

theorem missingIndex_gap (j : Fin 5) :
    -weights (missingIndex j).1 < (missingIndex j).2 ∧ (missingIndex j).2 < 0 := by
  fin_cases j <;> norm_num [missingIndex,weights]

theorem missingIndex_range : Set.range missingIndex =
    {p : Index | -weights p.1 < p.2 ∧ p.2 < 0} := by
  ext p
  constructor
  · rintro ⟨j,rfl⟩
    exact missingIndex_gap j
  · obtain ⟨i,n⟩ := p
    rintro ⟨hn,hn0⟩
    change -weights i < n at hn
    change n < 0 at hn0
    have hw : weights i ≤ 3 := by fin_cases i <;> norm_num [weights]
    have hlow : -2 ≤ n := by omega
    have hhigh : n ≤ -1 := by omega
    interval_cases n <;> fin_cases i <;> norm_num [weights] at hn
    all_goals decide +kernel

/-- The two chart ranges omit exactly the 5 displayed basis coefficients. -/
theorem allowed_union : positiveIndices ∪ negativeIndices = (Set.range missingIndex)ᶜ := by
  rw [missingIndex_range]
  ext p
  simp only [positiveIndices,negativeIndices,Set.mem_union,Set.mem_ofPred_eq,Set.mem_compl_iff]
  omega

def residue : Coefficients →ₗ[ℚ] (Fin 5 → ℚ) :=
  (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 5)).toLinearMap.comp
    (Finsupp.lcomapDomain missingIndex missingIndex_injective)

@[simp] theorem residue_apply (f : Coefficients) (j : Fin 5) :
    residue f j = f (missingIndex j) := rfl

theorem residue_surjective : Function.Surjective residue := by
  intro q
  let f : Fin 5 →₀ ℚ := (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 5)).symm q
  refine ⟨Finsupp.mapDomain missingIndex f,?_⟩
  funext j
  rw [residue_apply,Finsupp.mapDomain_apply_of_injective missingIndex_injective]
  rfl

theorem boundary_eq_ker : boundary = LinearMap.ker residue := by
  rw [boundary,positivePart,negativePart,←Finsupp.supported_union,allowed_union]
  ext f
  rw [Finsupp.mem_supported',LinearMap.mem_ker]
  constructor
  · intro h
    funext j
    exact h (missingIndex j) (by simp)
  · intro h p hp
    have hp' : p ∈ Set.range missingIndex := by simpa using hp
    obtain ⟨j,rfl⟩ := hp'
    exact congrFun h j

def quotientEquiv : (Coefficients ⧸ boundary) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ boundary_eq_ker).trans
    (residue.quotKerEquivOfSurjective residue_surjective)

theorem finrank_quotient : Module.finrank ℚ (Coefficients ⧸ boundary) = 5 := by
  simpa using quotientEquiv.finrank_eq

def positiveEight : Submodule ℚ EightLaurent := positivePart.map coordinatesEquiv.toLinearMap
def negativeEight : Submodule ℚ EightLaurent := negativePart.map coordinatesEquiv.toLinearMap
def boundaryEight : Submodule ℚ EightLaurent := positiveEight ⊔ negativeEight
def residueEight : EightLaurent →ₗ[ℚ] (Fin 5 → ℚ) :=
  residue.comp coordinatesEquiv.symm.toLinearMap

@[simp] theorem residueEight_apply (f : EightLaurent) (j : Fin 5) :
    residueEight f j = (f (missingIndex j).1).coeff (missingIndex j).2 := by
  change (coordinatesEquiv.symm f) (missingIndex j) = _
  exact (coordinatesEquiv_coeff (coordinatesEquiv.symm f) _ _).symm.trans
    (congrArg (fun x : EightLaurent => (x (missingIndex j).1).coeff (missingIndex j).2)
      (coordinatesEquiv.apply_symm_apply f))

theorem mem_positiveEight_iff (f : EightLaurent) :
    f ∈ positiveEight ↔ ∀ (i : Fin 8) (n : ℤ), n < 0 → (f i).coeff n = 0 := by
  rw [positiveEight,Submodule.mem_map]
  constructor
  · rintro ⟨g,hg,rfl⟩ i n hn
    have hs := (Finsupp.mem_supported' ℚ g).mp hg
    change (coordinatesEquiv g i).coeff n = 0
    rw [coordinatesEquiv_coeff]
    exact hs (i,n) (by change ¬0 ≤ n; omega)
  · intro h
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [positivePart,Finsupp.mem_supported']
    intro p hp
    have hn : p.2 < 0 := by change ¬0 ≤ p.2 at hp; omega
    have hc := coordinatesEquiv_coeff (coordinatesEquiv.symm f) p.1 p.2
    rw [coordinatesEquiv.apply_symm_apply] at hc
    exact hc.symm.trans (h p.1 p.2 hn)

theorem mem_negativeEight_iff (f : EightLaurent) :
    f ∈ negativeEight ↔ ∀ (i : Fin 8) (n : ℤ), -weights i < n → (f i).coeff n = 0 := by
  rw [negativeEight,Submodule.mem_map]
  constructor
  · rintro ⟨g,hg,rfl⟩ i n hn
    have hs := (Finsupp.mem_supported' ℚ g).mp hg
    change (coordinatesEquiv g i).coeff n = 0
    rw [coordinatesEquiv_coeff]
    exact hs (i,n) (by change ¬n ≤ -weights i; omega)
  · intro h
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [negativePart,Finsupp.mem_supported']
    intro p hp
    have hn : -weights p.1 < p.2 := by change ¬p.2 ≤ -weights p.1 at hp; omega
    have hc := coordinatesEquiv_coeff (coordinatesEquiv.symm f) p.1 p.2
    rw [coordinatesEquiv.apply_symm_apply] at hc
    exact hc.symm.trans (h p.1 p.2 hn)

def polynomialTupleMap : (Fin 8 → Polynomial ℚ) →ₗ[ℚ] EightLaurent :=
  LinearMap.pi fun i : Fin 8 =>
    (Polynomial.toLaurentAlg : Polynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ).toLinearMap.comp
      (LinearMap.proj i)

@[simp] theorem polynomialTupleMap_apply (f : Fin 8 → Polynomial ℚ) (i : Fin 8) :
    polynomialTupleMap f i = (f i).toLaurent := rfl

theorem polynomialTupleMap_range : LinearMap.range polynomialTupleMap = positiveEight := by
  ext f
  constructor
  · rintro ⟨q,rfl⟩
    apply (mem_positiveEight_iff _).mpr
    intro i
    exact (PositiveLaurentRange.polynomial_range_iff _).mp ⟨q i,rfl⟩
  · intro hf
    have hq : ∀ i : Fin 8, ∃ q : Polynomial ℚ, q.toLaurent = f i :=
      fun i => (PositiveLaurentRange.polynomial_range_iff _).mpr
        ((mem_positiveEight_iff _).mp hf i)
    choose q hq using hq
    exact ⟨q,funext hq⟩

def weightedReverse (f : EightLaurent) (i : Fin 8) : LaurentPolynomial ℚ :=
  LaurentPolynomial.invert (f i) * LaurentPolynomial.T (-weights i)

theorem weightedReverse_involutive (f : EightLaurent) : weightedReverse (weightedReverse f) = f := by
  funext i
  simp only [weightedReverse,map_mul,LaurentPolynomial.invert_T,neg_neg]
  rw [mul_assoc,←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,mul_one]
  exact LaurentPolynomial.involutive_invert (f i)

theorem weightedReverse_coeff (f : EightLaurent) (i : Fin 8) (n : ℤ) :
    (weightedReverse f i).coeff n = (f i).coeff (-n-weights i) := by
  simp only [weightedReverse,LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one,LaurentPolynomial.invert_apply]
  congr 1
  omega

theorem weightedReverse_mem_negative_iff (f : EightLaurent) :
    weightedReverse f ∈ negativeEight ↔ f ∈ positiveEight := by
  rw [mem_negativeEight_iff,mem_positiveEight_iff]
  constructor
  · intro h i n hn
    have hh := h i (-n-weights i) (by omega)
    rw [weightedReverse_coeff] at hh
    have he : -(-n-weights i)-weights i = n := by omega
    rwa [he] at hh
  · intro h i n hn
    rw [weightedReverse_coeff]
    exact h i (-n-weights i) (by omega)

theorem boundaryEight_eq_map : boundaryEight = boundary.map coordinatesEquiv.toLinearMap := by
  rw [boundaryEight,positiveEight,negativeEight,boundary,Submodule.map_sup]

theorem boundaryEight_eq_ker : boundaryEight = LinearMap.ker residueEight := by
  rw [boundaryEight_eq_map]
  ext f
  rw [Submodule.mem_map,LinearMap.mem_ker]
  constructor
  · rintro ⟨g,hg,rfl⟩
    change residue (coordinatesEquiv.symm (coordinatesEquiv g)) = 0
    rw [coordinatesEquiv.symm_apply_apply]
    exact LinearMap.mem_ker.mp (boundary_eq_ker ▸ hg)
  · intro hf
    refine ⟨coordinatesEquiv.symm f,?_,coordinatesEquiv.apply_symm_apply f⟩
    rw [boundary_eq_ker,LinearMap.mem_ker]
    exact hf

theorem residueEight_surjective : Function.Surjective residueEight := by
  intro q
  obtain ⟨g,hg⟩ := residue_surjective q
  refine ⟨coordinatesEquiv g,?_⟩
  change residue (coordinatesEquiv.symm (coordinatesEquiv g)) = q
  simpa only [coordinatesEquiv.symm_apply_apply] using hg

/-- Quotient by the two explicit Laurent chart coefficient ranges. -/
def quotientEightEquiv : (EightLaurent ⧸ boundaryEight) ≃ₗ[ℚ] (Fin 5 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ boundaryEight_eq_ker).trans
    (residueEight.quotKerEquivOfSurjective residueEight_surjective)

theorem finrank_eight_quotient : Module.finrank ℚ (EightLaurent ⧸ boundaryEight) = 5 := by
  simpa using quotientEightEquiv.finrank_eq

def constantIndex : Index := (0,0)

theorem allowed_intersection : positiveIndices ∩ negativeIndices = {constantIndex} := by
  ext p
  obtain ⟨i,n⟩ := p
  fin_cases i <;> simp [positiveIndices,negativeIndices,weights,constantIndex] <;> omega

theorem intersection_coefficients :
    positivePart ⊓ negativePart = Finsupp.supported ℚ ℚ {constantIndex} := by
  rw [positivePart,negativePart,←Finsupp.supported_inter,allowed_intersection]

theorem coefficient_normal_form (f : Coefficients) (hf : f ∈ positivePart ⊓ negativePart) :
    f = Finsupp.single constantIndex (f constantIndex) := by
  rw [intersection_coefficients,Finsupp.mem_supported'] at hf
  ext p
  by_cases hp : p = constantIndex
  · subst p; simp
  · have hz : f p = 0 := hf p (by simpa using hp)
    simp [hp,hz]

def constantEight : ℚ →ₗ[ℚ] EightLaurent :=
  coordinatesEquiv.toLinearMap.comp (Finsupp.lsingle constantIndex)

@[simp] theorem constantEight_coeff (q : ℚ) (i : Fin 8) (n : ℤ) :
    (constantEight q i).coeff n = Finsupp.single constantIndex q (i,n) := rfl

theorem constantEight_mem (q : ℚ) : constantEight q ∈ positiveEight ⊓ negativeEight := by
  constructor
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [positiveIndices,constantIndex]),rfl⟩
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [negativeIndices,constantIndex,weights]),rfl⟩

theorem eight_normal_form (f : EightLaurent) (hf : f ∈ positiveEight ⊓ negativeEight) :
    f = constantEight ((f 0).coeff 0) := by
  obtain ⟨g,hgp,hgf⟩ := hf.1
  obtain ⟨h,hhn,hhf⟩ := hf.2
  have hgh : g = h := coordinatesEquiv.injective (hgf.trans hhf.symm)
  subst h
  have hn := coefficient_normal_form g ⟨hgp,hhn⟩
  have hc : (f 0).coeff 0 = g constantIndex := by rw [←hgf]; rfl
  rw [hc,←hgf]
  exact congrArg coordinatesEquiv hn

def intersectionEightEquiv : ↥(positiveEight ⊓ negativeEight) ≃ₗ[ℚ] ℚ where
  toFun f := (f.1 0).coeff 0
  invFun q := ⟨constantEight q,constantEight_mem q⟩
  left_inv f := Subtype.ext (eight_normal_form f.1 f.2).symm
  right_inv q := by simp [constantEight_coeff,constantIndex]
  map_add' f g := by simp
  map_smul' q f := by simp

theorem finrank_eight_intersection : Module.finrank ℚ ↥(positiveEight ⊓ negativeEight) = 1 := by
  simpa using intersectionEightEquiv.finrank_eq

end
end Z2Z4Rank6.ThirdTwistCoverLaurent
