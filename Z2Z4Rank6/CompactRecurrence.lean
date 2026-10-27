import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic

/-!
# Congruence neighborhoods in a compact group

The compact-group argument in Proposition 6.2 of Manvir Jaswal,
*Infinitely many elliptic curves with torsion Z/2Z × Z/4Z and rank at least six*,
DOI 10.5281/zenodo.23437117.

The theorem isolates the finite-translate argument from the realization of the
curve as a compact group over the finitely many local fields.
-/

open Set Filter
open scoped Topology Pointwise

namespace Z2Z4Rank6

/-- An infinite subgroup of a compact topological additive group has infinitely
many elements in each neighborhood of zero. -/
theorem infinite_subgroup_inter_nhds_zero
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G]
    (H : AddSubgroup G) (hH : (H : Set G).Infinite)
    {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ((H : Set G) ∩ U).Infinite := by
  classical
  obtain ⟨V, hV, _, hneg, hVV⟩ := exists_closed_nhds_zero_neg_eq_add_subset hU
  let W := interior V
  have hW0 : (0 : G) ∈ W := mem_interior_iff_mem_nhds.mpr hV
  let T : G → Set G := fun x => {y | y - x ∈ W}
  have hTopen : ∀ x, IsOpen (T x) := by
    intro x
    exact isOpen_interior.preimage (continuous_id.sub continuous_const)
  have hTcover : (univ : Set G) ⊆ ⋃ x, T x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, by simpa [T] using hW0⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover T hTopen hTcover
  intro hfinite
  have hpieces : ∀ x, ((H : Set G) ∩ T x).Finite := by
    intro x
    by_cases hnonempty : ((H : Set G) ∩ T x).Nonempty
    · obtain ⟨y0, hy0H, hy0T⟩ := hnonempty
      have hy0V : y0 - x ∈ V := interior_subset hy0T
      have hn : -(y0 - x) ∈ -V := by simpa using hy0V
      rw [hneg] at hn
      have himage : (fun y : G => y - y0) '' ((H : Set G) ∩ T x) ⊆
          (H : Set G) ∩ U := by
        rintro _ ⟨y, ⟨hyH, hyT⟩, rfl⟩
        refine ⟨H.sub_mem hyH hy0H, ?_⟩
        have hyV : y - x ∈ V := interior_subset hyT
        have hsum : (y - x) + -(y0 - x) ∈ U :=
          hVV (add_mem_add hyV hn)
        convert hsum using 1
        abel_nf
      exact (hfinite.subset himage).of_finite_image (by
        intro y _ z _ heq
        have heq' := congrArg (fun w : G => w + y0) heq
        simpa only [sub_add_cancel] using heq')
    · exact (not_nonempty_iff_eq_empty.mp hnonempty) ▸ finite_empty
  apply hH
  apply (t.finite_toSet.biUnion (fun x _ => hpieces x)).subset
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  exact mem_iUnion₂.mpr ⟨x, hxt, hy, hyx⟩

/-- The same finite-translate argument at any element of the subgroup. -/
theorem infinite_subgroup_inter_nhds
    {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G]
    (H : AddSubgroup G) (hH : (H : Set G).Infinite)
    {a : G} (ha : a ∈ H) {U : Set G} (hU : U ∈ 𝓝 a) :
    ((H : Set G) ∩ U).Infinite := by
  let V : Set G := (fun z : G => z+a) ⁻¹' U
  have hV : V ∈ 𝓝 (0 : G) := by
    have hc : Continuous (fun z : G => z+a) := continuous_id.add continuous_const
    have ht : Tendsto (fun z : G => z+a) (𝓝 (0 : G)) (𝓝 a) := by
      simpa only [zero_add] using hc.tendsto (0 : G)
    exact ht.eventually hU
  have hinf := infinite_subgroup_inter_nhds_zero H hH hV
  have himage : ((fun z : G => z+a) '' ((H : Set G) ∩ V)).Infinite :=
    hinf.image (by intro x _ y _ he; exact add_right_cancel he)
  apply himage.mono
  rintro _ ⟨x,⟨hxH,hxV⟩,rfl⟩
  exact ⟨H.add_mem hxH ha,hxV⟩

/-- In a compact group, the preimage of a neighborhood of an embedded point
contains infinitely many elements of an infinite embedded group. -/
theorem infinite_preimage_nhds_of_injective
    {A G : Type*} [AddCommGroup A] [Infinite A]
    [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G]
    (f : A →+ G) (hf : Function.Injective f) (a : A)
    {U : Set G} (hU : U ∈ 𝓝 (f a)) : (f ⁻¹' U).Infinite := by
  have hH : (f.range : Set G).Infinite := by
    exact Set.infinite_range_of_injective hf
  have hi := infinite_subgroup_inter_nhds f.range hH (a := f a) ⟨a,rfl⟩ hU
  have hp : (f ⁻¹' ((f.range : Set G) ∩ U)).Infinite :=
    hi.preimage (fun _ hy => hy.1)
  exact hp.mono (fun _ hx => hx.2)

end Z2Z4Rank6
