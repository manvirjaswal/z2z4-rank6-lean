module

public import Z2Z4Rank6.TripleSquareBasisValues
public import Z2Z4Rank6.ThirdTwistCoverInfinity

@[expose] public section

/-! The third-twist affine and infinity rings have free
polynomial bases 1,u,v,uv,r,ur,vr,uvr (respectively 1,U,V,UV,R,UR,VR,UVR). -/
namespace Z2Z4Rank6.ThirdTwistCoverAffine
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev basis  := TripleSquareCover.coordinateBasis (radicand)
instance moduleFinite  : Module.Finite Poly (CoordinateRing) := Module.Finite.of_basis (basis)
instance nontrivial  : Nontrivial (CoordinateRing) := TripleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.ThirdTwistCoverAffine
namespace Z2Z4Rank6.ThirdTwistCoverInfinity
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev basis  := TripleSquareCover.coordinateBasis (radicand)
instance moduleFinite  : Module.Finite Poly (CoordinateRing) := Module.Finite.of_basis (basis)
instance nontrivial  : Nontrivial (CoordinateRing) := TripleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.ThirdTwistCoverInfinity
