import Definitions.Def_AngelDevil_NiceReduction
open AngelDevil
theorem AngelDevil.confinement_to_nice (p N : Nat) (D : DevilStrategy)
    (hc : ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) : NiceCanConfine p N  := by sorry
