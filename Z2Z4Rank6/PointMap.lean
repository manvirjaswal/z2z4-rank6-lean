module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Common.Elliptic.WeierstrassCoordinates

@[expose] public section

/-!
# Point-group maps induced by field embeddings

This uses Mathlib's elliptic-curve group law and field base-change map.
It supplies the coordinate compatibility used for Proposition 5.1 of Manvir
Jaswal, DOI 10.5281/zenodo.23437117.
-/

namespace Z2Z4Rank6
noncomputable section

open Common.WeierstrassCoordinates

/-- The Mathlib point-group map induced by a field embedding. -/
def fieldPointMap {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) (W : WeierstrassCurve F) :
    W.toAffine.Point →+ (W.map f).toAffine.Point := by
  letI : Algebra F L := f.toAlgebra
  exact WeierstrassCurve.Affine.Point.map
    (R := F) (S := F) (F := F) (K := L) (W' := W) (Algebra.ofId F L)

/-- The field-induced point map acts on affine coordinates by the given embedding. -/
theorem encode_fieldPointMap {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    encode (fieldPointMap f W P) = (encode P).map (fun xy => (f xy.1,f xy.2)) := by
  cases P <;> rfl

end
end Z2Z4Rank6
