import Z2Z4Rank6.GTorsionCoverDoubleBasis
import Z2Z4Rank6.GTorsionCoverInfinity

/-! The signed affine and infinity torsion-cover rings have free
polynomial bases 1,u,r,ur (respectively 1,U,R,UR). -/
namespace Z2Z4Rank6.GTorsionCoverAffine
noncomputable section
abbrev Poly := DoubleSquareCover.Poly
abbrev basis (ε : Bool) := DoubleSquareCover.coordinateBasis (radicand ε)
instance moduleFinite (ε : Bool) : Module.Finite Poly (CoordinateRing ε) := Module.Finite.of_basis (basis ε)
instance nontrivial (ε : Bool) : Nontrivial (CoordinateRing ε) := DoubleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.GTorsionCoverAffine
namespace Z2Z4Rank6.GTorsionCoverInfinity
noncomputable section
abbrev Poly := DoubleSquareCover.Poly
abbrev basis (ε : Bool) := DoubleSquareCover.coordinateBasis (radicand ε)
instance moduleFinite (ε : Bool) : Module.Finite Poly (CoordinateRing ε) := Module.Finite.of_basis (basis ε)
instance nontrivial (ε : Bool) : Nontrivial (CoordinateRing ε) := DoubleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.GTorsionCoverInfinity
