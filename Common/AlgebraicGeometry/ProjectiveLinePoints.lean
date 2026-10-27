import Common.AlgebraicGeometry.ProjectiveLine

/-! Finite and infinity coordinate points of P1 are distinct. -/
namespace AlgebraicGeometry.ProjectiveLine
noncomputable section
open CategoryTheory MvPolynomial
open scoped Classical
variable (k : Type) [Field k]

abbrev sourcePoint : Spec (CommRingCat.of k) := ProjValuedPoint.sourcePoint (K:=k)

theorem affinePoint_mem_basicOpen (t : k) (f : Ring k) (hf : f∈grading k 1) :
    affinePoint k k t (sourcePoint k)∈Proj.basicOpen (grading k) f ↔
      (MvPolynomial.aeval ![t,1]) f≠0 :=
  ProjValuedPoint.point_mem_basicOpen (grading k) (MvPolynomial.aeval ![t,1])
    (by decide : 0<1) (coordinate k 1) (coordinate_degree k 1) (by simp [coordinate])
    (by decide : 0<1) f hf

theorem infinityPoint_mem_basicOpen (f : Ring k) (hf : f∈grading k 1) :
    infinityPoint k k (sourcePoint k)∈Proj.basicOpen (grading k) f ↔
      (MvPolynomial.aeval ![(1:k),0]) f≠0 :=
  ProjValuedPoint.point_mem_basicOpen (grading k) (MvPolynomial.aeval ![(1:k),0])
    (by decide : 0<1) (coordinate k 0) (coordinate_degree k 0) (by simp [coordinate])
    (by decide : 0<1) f hf

theorem affinePoint_injective : Function.Injective (affinePoint k k) := by
  intro s t h
  let f : Ring k := X 0-C s*X 1
  have hf : f∈grading k 1 :=
    (isHomogeneous_X k (0 : Fin 2)).sub ((isHomogeneous_X k (1 : Fin 2)).C_mul s)
  have hs : (MvPolynomial.aeval ![s,1]) f=0 := by simp [f]
  have ht : (MvPolynomial.aeval ![t,1]) f=0 := by
    by_contra hz
    have hmt := (affinePoint_mem_basicOpen k t f hf).mpr hz
    have hms : affinePoint k k s (sourcePoint k)∉Proj.basicOpen (grading k) f := by
      rw [affinePoint_mem_basicOpen k s f hf]
      simp only [hs,ne_eq,not_true_eq_false,not_false_eq_true]
    apply hms
    rw [h]
    exact hmt
  have he : t-s=0 := by simpa [f] using ht
  exact (sub_eq_zero.mp he).symm

theorem infinityPoint_ne_affinePoint (t : k) : infinityPoint k k≠affinePoint k k t := by
  intro h
  have hp : affinePoint k k t (sourcePoint k)∈Proj.basicOpen (grading k) (coordinate k 1) := by
    rw [affinePoint_mem_basicOpen _ _ _ (coordinate_degree k 1)]
    simp [coordinate]
  have hi : infinityPoint k k (sourcePoint k)∉Proj.basicOpen (grading k) (coordinate k 1) := by
    rw [infinityPoint_mem_basicOpen _ _ (coordinate_degree k 1)]
    simp [coordinate]
  exact hi (h ▸ hp)

def parameterPoint : Option k → (Spec (CommRingCat.of k) ⟶ scheme k)
  | some t=>affinePoint k k t
  | none=>infinityPoint k k

theorem parameterPoint_injective : Function.Injective (parameterPoint k) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none=>rfl
    | some t=>exact False.elim (infinityPoint_ne_affinePoint k t h)
  | some s =>
    cases b with
    | none=>exact False.elim (infinityPoint_ne_affinePoint k s h.symm)
    | some t=>exact congrArg some (affinePoint_injective k h)

end
end AlgebraicGeometry.ProjectiveLine
