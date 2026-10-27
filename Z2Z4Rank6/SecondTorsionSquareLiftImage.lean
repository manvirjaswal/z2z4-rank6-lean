module

public import Z2Z4Rank6.SecondTorsionSquareLiftData

@[expose] public section

/-! Pure image transport for the signed square lifts. -/
namespace Z2Z4Rank6.SecondTorsionHyperelliptic

theorem signed_square_locus_eq_lift_range (ε : Bool) :
    {c : SecondFamily.G2Point ℚ | IsSquare (sign ε*SecondFamily.V c.W)}=
      Set.range (fun P : SquareLift ε => P.c) := by
  ext c
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨⟨c,r,by rw [pow_two];exact hr.symm⟩,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨P.r,by rw [←pow_two];exact P.r_sq.symm⟩

theorem finite_signed_square_locus_of_finite_lifts (ε : Bool) [Finite (SquareLift ε)] :
    {c : SecondFamily.G2Point ℚ | IsSquare (sign ε*SecondFamily.V c.W)}.Finite := by
  rw [signed_square_locus_eq_lift_range]
  exact Set.finite_range _

end Z2Z4Rank6.SecondTorsionHyperelliptic
