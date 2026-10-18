import Definitions.Def_AngelDevil_Game
open AngelDevil
theorem AngelDevil.uniform_confinement (p : Nat) (hp : 0 < p)
    (h : ¬ AngelWins p) : ∃ N, 0 < N ∧ ∃ D : DevilStrategy,
    ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n)) := by sorry
