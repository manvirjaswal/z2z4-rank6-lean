import Z2Z4Rank6.TripleSquareBasisValues
import Z2Z4Rank6.SecondTorsionCoverInfinity

/-! The signed affine and infinity torsion-cover rings have free
polynomial bases 1,u,v,uv,r,ur,vr,uvr (respectively 1,U,V,UV,R,UR,VR,UVR). -/
namespace Z2Z4Rank6.SecondTorsionCoverAffine
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev basis (ε : Bool) := TripleSquareCover.coordinateBasis (radicand ε)
instance moduleFinite (ε : Bool) : Module.Finite Poly (CoordinateRing ε) := Module.Finite.of_basis (basis ε)
instance nontrivial (ε : Bool) : Nontrivial (CoordinateRing ε) := TripleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.SecondTorsionCoverAffine
namespace Z2Z4Rank6.SecondTorsionCoverInfinity
noncomputable section
abbrev Poly := TripleSquareCover.Poly
abbrev basis (ε : Bool) := TripleSquareCover.coordinateBasis (radicand ε)
instance moduleFinite (ε : Bool) : Module.Finite Poly (CoordinateRing ε) := Module.Finite.of_basis (basis ε)
instance nontrivial (ε : Bool) : Nontrivial (CoordinateRing ε) := TripleSquareCover.coordinateRing_nontrivial _
end
end Z2Z4Rank6.SecondTorsionCoverInfinity
