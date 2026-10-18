import Theorems.Thm_AngelDevil_nice_devil_reduction
import Theorems.Thm_AngelDevil_power_two_beats_nice_devil

/-! A tracked reduction, not a closed proof: both imported paper milestones
are currently open on Prove2Me. This file is checked separately from Foundation.
-/
theorem solution : AngelDevil.AngelWins 2 := by
  apply Classical.byContradiction
  intro h
  obtain ⟨N, _, D, hNice, hConfine⟩ :=
    AngelDevil.nice_devil_reduction 2 (by decide) h
  obtain ⟨A, hA⟩ := AngelDevil.power_two_beats_nice_devil
  obtain ⟨hSafe, hEscape⟩ := hA D hNice
  obtain ⟨n, hn⟩ := hEscape N
  exact hn (hConfine A n (fun m _ => hSafe m))
