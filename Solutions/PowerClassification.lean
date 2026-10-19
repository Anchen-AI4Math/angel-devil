import Solutions.Completed
import Solutions.KingCapture

namespace AngelDevil

theorem survives_mono {p q : Nat} (hpq : p ≤ q)
    {A : AngelStrategy} {D : DevilStrategy} (h : Survives p A D) :
    Survives q A D := by
  intro n
  exact ⟨jump_mono hpq (h n).1, (h n).2⟩

theorem angelWins_mono {p q : Nat} (hpq : p ≤ q)
    (h : AngelWins p) : AngelWins q := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun D => survives_mono hpq (hA D)⟩

theorem power_ge_two_wins (p : Nat) (hp : 2 ≤ p) : AngelWins p :=
  angelWins_mono hp power_two_wins

theorem power_le_one_devil_wins (p : Nat) (hp : p ≤ 1) :
    ∃ D : DevilStrategy, ∀ A, ¬ Survives p A D := by
  obtain ⟨D,hD⟩ := power_one_devil_wins
  exact ⟨D, fun A hA => hD A (survives_mono hp hA)⟩

/-- Complete classification, including the degenerate natural-number power 0. -/
theorem angelWins_iff_two_le (p : Nat) : AngelWins p ↔ 2 ≤ p := by
  constructor
  · intro h
    by_contra hp
    exact power_one_not_wins (angelWins_mono (by omega) h)
  · exact power_ge_two_wins p

theorem devilWins_iff_le_one (p : Nat) :
    (∃ D : DevilStrategy, ∀ A, ¬ Survives p A D) ↔ p ≤ 1 := by
  constructor
  · rintro ⟨D,hD⟩
    by_contra hp
    obtain ⟨A,hA⟩ := power_ge_two_wins p (by omega)
    exact hD A (hA D)
  · exact power_le_one_devil_wins p

end AngelDevil
