import Theorems.Thm_AngelDevil_uniform_confinement
import Theorems.Thm_AngelDevil_confinement_to_nice

theorem solution (p : Nat) (hp : 0 < p) :
    ¬ AngelDevil.AngelWins p → ∃ N, 0 < N ∧ AngelDevil.NiceCanConfine p N := by
  intro h
  obtain ⟨N, hN, D, hD⟩ := AngelDevil.uniform_confinement p hp h
  exact ⟨N, hN, AngelDevil.confinement_to_nice p N D hD⟩
