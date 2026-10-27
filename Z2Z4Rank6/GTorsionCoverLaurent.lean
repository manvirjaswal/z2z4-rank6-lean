import Z2Z4Rank6.LaurentCechQuotient
import Z2Z4Rank6.PositiveLaurentRange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Four Laurent components for the signed covers of G

The basis 1,u,r,ur has pole weights 0,2,4,6. The two chart coefficient
ranges leave 1+3+5=9 explicitly indexed coefficients. This is coefficient
algebra; chart maps and sheaf cohomology are connected later.
-/

namespace Z2Z4Rank6.GTorsionCoverLaurent
noncomputable section
open scoped Classical

abbrev Index := Fin 4 × ℤ
abbrev Coefficients := Index →₀ ℚ
abbrev FourLaurent := Fin 4 → LaurentPolynomial ℚ

def weights : Fin 4 → ℤ := ![0,2,4,6]
def positiveIndices : Set Index := {p | 0 ≤ p.2}
def negativeIndices : Set Index := {p | p.2 ≤ -weights p.1}

/-- The missing coefficients, in basis order and decreasing exponent. -/
def missingIndex : Fin 9 → Index :=
  ![(1,-1),(2,-1),(2,-2),(2,-3),(3,-1),(3,-2),(3,-3),(3,-4),(3,-5)]

theorem missingIndex_injective : Function.Injective missingIndex := by decide +kernel

def coordinatesEquiv : Coefficients ≃ₗ[ℚ] FourLaurent :=
  ((Finsupp.curryLinearEquiv ℚ).trans
    (Finsupp.linearEquivFunOnFinite ℚ (ℤ →₀ ℚ) (Fin 4))).trans
      (LinearEquiv.piCongrRight fun _ : Fin 4 =>
        (AddMonoidAlgebra.coeffLinearEquiv ℚ : LaurentPolynomial ℚ ≃ₗ[ℚ] (ℤ →₀ ℚ)).symm)

@[simp] theorem coordinatesEquiv_coeff (f : Coefficients) (i : Fin 4) (n : ℤ) :
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

theorem missingIndex_gap (j : Fin 9) :
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
    have hw : weights i ≤ 6 := by fin_cases i <;> norm_num [weights]
    have hlow : -5 ≤ n := by omega
    have hhigh : n ≤ -1 := by omega
    interval_cases n <;> fin_cases i <;> norm_num [weights] at hn
    all_goals decide +kernel

/-- The two chart ranges omit exactly the 9 displayed basis coefficients. -/
theorem allowed_union : positiveIndices ∪ negativeIndices = (Set.range missingIndex)ᶜ := by
  rw [missingIndex_range]
  ext p
  simp only [positiveIndices,negativeIndices,Set.mem_union,Set.mem_ofPred_eq,Set.mem_compl_iff]
  omega

def residue : Coefficients →ₗ[ℚ] (Fin 9 → ℚ) :=
  (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 9)).toLinearMap.comp
    (Finsupp.lcomapDomain missingIndex missingIndex_injective)

@[simp] theorem residue_apply (f : Coefficients) (j : Fin 9) :
    residue f j = f (missingIndex j) := rfl

theorem residue_surjective : Function.Surjective residue := by
  intro q
  let f : Fin 9 →₀ ℚ := (Finsupp.linearEquivFunOnFinite ℚ ℚ (Fin 9)).symm q
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

def quotientEquiv : (Coefficients ⧸ boundary) ≃ₗ[ℚ] (Fin 9 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ boundary_eq_ker).trans
    (residue.quotKerEquivOfSurjective residue_surjective)

theorem finrank_quotient : Module.finrank ℚ (Coefficients ⧸ boundary) = 9 := by
  simpa using quotientEquiv.finrank_eq

def positiveFour : Submodule ℚ FourLaurent := positivePart.map coordinatesEquiv.toLinearMap
def negativeFour : Submodule ℚ FourLaurent := negativePart.map coordinatesEquiv.toLinearMap
def boundaryFour : Submodule ℚ FourLaurent := positiveFour ⊔ negativeFour
def residueFour : FourLaurent →ₗ[ℚ] (Fin 9 → ℚ) :=
  residue.comp coordinatesEquiv.symm.toLinearMap

@[simp] theorem residueFour_apply (f : FourLaurent) (j : Fin 9) :
    residueFour f j = (f (missingIndex j).1).coeff (missingIndex j).2 := by
  change (coordinatesEquiv.symm f) (missingIndex j) = _
  exact (coordinatesEquiv_coeff (coordinatesEquiv.symm f) _ _).symm.trans
    (congrArg (fun x : FourLaurent => (x (missingIndex j).1).coeff (missingIndex j).2)
      (coordinatesEquiv.apply_symm_apply f))

theorem mem_positiveFour_iff (f : FourLaurent) :
    f ∈ positiveFour ↔ ∀ (i : Fin 4) (n : ℤ), n < 0 → (f i).coeff n = 0 := by
  rw [positiveFour,Submodule.mem_map]
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

theorem mem_negativeFour_iff (f : FourLaurent) :
    f ∈ negativeFour ↔ ∀ (i : Fin 4) (n : ℤ), -weights i < n → (f i).coeff n = 0 := by
  rw [negativeFour,Submodule.mem_map]
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

def polynomialTupleMap : (Fin 4 → Polynomial ℚ) →ₗ[ℚ] FourLaurent :=
  LinearMap.pi fun i : Fin 4 =>
    (Polynomial.toLaurentAlg : Polynomial ℚ →ₐ[ℚ] LaurentPolynomial ℚ).toLinearMap.comp
      (LinearMap.proj i)

@[simp] theorem polynomialTupleMap_apply (f : Fin 4 → Polynomial ℚ) (i : Fin 4) :
    polynomialTupleMap f i = (f i).toLaurent := rfl

theorem polynomialTupleMap_range : LinearMap.range polynomialTupleMap = positiveFour := by
  ext f
  constructor
  · rintro ⟨q,rfl⟩
    apply (mem_positiveFour_iff _).mpr
    intro i
    exact (PositiveLaurentRange.polynomial_range_iff _).mp ⟨q i,rfl⟩
  · intro hf
    have hq : ∀ i : Fin 4, ∃ q : Polynomial ℚ, q.toLaurent = f i :=
      fun i => (PositiveLaurentRange.polynomial_range_iff _).mpr
        ((mem_positiveFour_iff _).mp hf i)
    choose q hq using hq
    exact ⟨q,funext hq⟩

def weightedReverse (f : FourLaurent) (i : Fin 4) : LaurentPolynomial ℚ :=
  LaurentPolynomial.invert (f i) * LaurentPolynomial.T (-weights i)

theorem weightedReverse_involutive (f : FourLaurent) : weightedReverse (weightedReverse f) = f := by
  funext i
  simp only [weightedReverse,map_mul,LaurentPolynomial.invert_T,neg_neg]
  rw [mul_assoc,←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,mul_one]
  exact LaurentPolynomial.involutive_invert (f i)

theorem weightedReverse_coeff (f : FourLaurent) (i : Fin 4) (n : ℤ) :
    (weightedReverse f i).coeff n = (f i).coeff (-n-weights i) := by
  simp only [weightedReverse,LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,
    mul_one,LaurentPolynomial.invert_apply]
  congr 1
  omega

theorem weightedReverse_mem_negative_iff (f : FourLaurent) :
    weightedReverse f ∈ negativeFour ↔ f ∈ positiveFour := by
  rw [mem_negativeFour_iff,mem_positiveFour_iff]
  constructor
  · intro h i n hn
    have hh := h i (-n-weights i) (by omega)
    rw [weightedReverse_coeff] at hh
    have he : -(-n-weights i)-weights i = n := by omega
    rwa [he] at hh
  · intro h i n hn
    rw [weightedReverse_coeff]
    exact h i (-n-weights i) (by omega)

theorem boundaryFour_eq_map : boundaryFour = boundary.map coordinatesEquiv.toLinearMap := by
  rw [boundaryFour,positiveFour,negativeFour,boundary,Submodule.map_sup]

theorem boundaryFour_eq_ker : boundaryFour = LinearMap.ker residueFour := by
  rw [boundaryFour_eq_map]
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

theorem residueFour_surjective : Function.Surjective residueFour := by
  intro q
  obtain ⟨g,hg⟩ := residue_surjective q
  refine ⟨coordinatesEquiv g,?_⟩
  change residue (coordinatesEquiv.symm (coordinatesEquiv g)) = q
  simpa only [coordinatesEquiv.symm_apply_apply] using hg

/-- Quotient by the two explicit Laurent chart coefficient ranges. -/
def quotientFourEquiv : (FourLaurent ⧸ boundaryFour) ≃ₗ[ℚ] (Fin 9 → ℚ) :=
  (Submodule.quotEquivOfEq _ _ boundaryFour_eq_ker).trans
    (residueFour.quotKerEquivOfSurjective residueFour_surjective)

theorem finrank_four_quotient : Module.finrank ℚ (FourLaurent ⧸ boundaryFour) = 9 := by
  simpa using quotientFourEquiv.finrank_eq

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

def constantFour : ℚ →ₗ[ℚ] FourLaurent :=
  coordinatesEquiv.toLinearMap.comp (Finsupp.lsingle constantIndex)

@[simp] theorem constantFour_coeff (q : ℚ) (i : Fin 4) (n : ℤ) :
    (constantFour q i).coeff n = Finsupp.single constantIndex q (i,n) := rfl

theorem constantFour_mem (q : ℚ) : constantFour q ∈ positiveFour ⊓ negativeFour := by
  constructor
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [positiveIndices,constantIndex]),rfl⟩
  · exact ⟨Finsupp.single constantIndex q,
      Finsupp.single_mem_supported ℚ q (by simp [negativeIndices,constantIndex,weights]),rfl⟩

theorem four_normal_form (f : FourLaurent) (hf : f ∈ positiveFour ⊓ negativeFour) :
    f = constantFour ((f 0).coeff 0) := by
  obtain ⟨g,hgp,hgf⟩ := hf.1
  obtain ⟨h,hhn,hhf⟩ := hf.2
  have hgh : g = h := coordinatesEquiv.injective (hgf.trans hhf.symm)
  subst h
  have hn := coefficient_normal_form g ⟨hgp,hhn⟩
  have hc : (f 0).coeff 0 = g constantIndex := by rw [←hgf]; rfl
  rw [hc,←hgf]
  exact congrArg coordinatesEquiv hn

def intersectionFourEquiv : ↥(positiveFour ⊓ negativeFour) ≃ₗ[ℚ] ℚ where
  toFun f := (f.1 0).coeff 0
  invFun q := ⟨constantFour q,constantFour_mem q⟩
  left_inv f := Subtype.ext (four_normal_form f.1 f.2).symm
  right_inv q := by simp [constantFour_coeff,constantIndex]
  map_add' f g := by simp
  map_smul' q f := by simp

theorem finrank_four_intersection : Module.finrank ℚ ↥(positiveFour ⊓ negativeFour) = 1 := by
  simpa using intersectionFourEquiv.finrank_eq

end
end Z2Z4Rank6.GTorsionCoverLaurent
