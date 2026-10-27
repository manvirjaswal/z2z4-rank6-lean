module

public import Z2Z4Rank6.TorsionSquareLiftData

@[expose] public section

/-! Pure image transport for the signed square lifts. -/
namespace Z2Z4Rank6.TorsionHyperelliptic

theorem signed_square_locus_eq_lift_range (ε : Bool) :
    {c : CPoint | IsSquare (sign ε*a c.m*b c.m)}=
      Set.range (fun P : SquareLift ε => P.c) := by
  ext c
  constructor
  · rintro ⟨r,hr⟩
    exact ⟨⟨c,r,by rw [pow_two];exact hr.symm⟩,rfl⟩
  · rintro ⟨P,rfl⟩
    exact ⟨P.r,by rw [←pow_two];exact P.r_sq.symm⟩

theorem finite_signed_square_locus_of_finite_lifts (ε : Bool) [Finite (SquareLift ε)] :
    {c : CPoint | IsSquare (sign ε*a c.m*b c.m)}.Finite := by
  rw [signed_square_locus_eq_lift_range]
  exact Set.finite_range _

end Z2Z4Rank6.TorsionHyperelliptic
