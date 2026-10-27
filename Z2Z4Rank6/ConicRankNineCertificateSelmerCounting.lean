module

public import Z2Z4Rank6.TwistSelmerDataSieve

@[expose] public section

/-! Finite cardinal bounds for the free-bit reconstruction pool.
The proof counts the domain of the explicit candidate map. -/
namespace Z2Z4Rank6.ConicRankNineCertificate.Selmer
open Z2Z4Rank6.TwistSelmer
noncomputable section

/-- The image of all free bit vectors under the candidate map. -/
def finiteKernelPool {s f : ℕ} (ps : Fin s→ℕ)
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2)) : Finset ECFullTriple := by
  classical
  exact Finset.univ.image (fun v : Fin f→ZMod 2 => candidate ps (N.mulVec v))

theorem mem_finiteKernelPool {s f : ℕ} (ps : Fin s→ℕ)
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2))
    (d : ECFullTriple) (hd : d∈decodedPool ps N) : d∈finiteKernelPool ps N := by
  classical
  obtain ⟨v,_,hv⟩ := List.mem_map.mp hd
  exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,hv⟩

theorem finiteKernelPool_card_le {s f : ℕ} (ps : Fin s→ℕ)
    (N : Matrix (Fin (BitDimension s)) (Fin f) (ZMod 2)) :
    (finiteKernelPool ps N).card≤2^f := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Fin f→ZMod 2)).card := Finset.card_image_le
    _ = 2^f := by simp

end
end Z2Z4Rank6.ConicRankNineCertificate.Selmer
