import Z2Z4Rank6.ECFullSelmerCertificate
import Z2Z4Rank6.ECFullSelmerVector

/-!
# The full split two-Selmer certificate for E_C

The explicit everywhere-locally-soluble squareclass model has dimension 3.
Paper source: Jaswal, Lemma 4.1(b), DOI 10.5281/zenodo.23437117.
-/
namespace Z2Z4Rank6

theorem ec_fullTwoSelmerClasses_eq_space :
    fullTwoSelmerClasses 729 484 = (ecFullSelmerSpace : Set _) := by
  rw [fullTwoSelmerClasses,ec_fullTwoSelmerTriples]
  exact ecFull_survivor_classes_eq_space

theorem ec_fullTwoSelmer_dimension :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (fullTwoSelmerClasses 729 484)) = 3 := by
  rw [ec_fullTwoSelmerClasses_eq_space,Submodule.span_eq]
  exact ecFullSelmerSpace_finrank

theorem ec_fullTwoSelmerClasses_card : (fullTwoSelmerClasses 729 484).ncard = 8 := by
  rw [ec_fullTwoSelmerClasses_eq_space]
  have heq := ecFull_survivor_classes_eq_space
  rw [←heq]
  have hinj : Set.InjOn
      (fun d : ECFullTriple => ecPairSquareClass (d.1 : ℚ) (d.2.1 : ℚ))
      (ecFullSurvivors.toFinset : Set ECFullTriple) := by
    intro d hd e he hde
    have hd' : d ∈ ecFullSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using hd
    have he' : e ∈ ecFullSurvivors := by simpa only [Finset.mem_coe,List.mem_toFinset] using he
    obtain ⟨i,rfl⟩ := (ecFullSurvivorTriple_mem_iff d).mp hd'
    obtain ⟨j,rfl⟩ := (ecFullSurvivorTriple_mem_iff e).mp he'
    dsimp only at hde
    rw [ecFull_survivor_class_formula,ecFull_survivor_class_formula] at hde
    have hc : ecFullCoefficients i = ecFullCoefficients j :=
      (linearIndependent_iff_injective_fintypeLinearCombination.mp ecFull_basis_independent) hde
    have hi : i = j := (by decide +kernel : Function.Injective ecFullCoefficients) hc
    rw [hi]
  rw [hinj.ncard_image,Set.ncard_coe_finset,ecFullSurvivors_card]

end Z2Z4Rank6
