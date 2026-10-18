import Definitions.Def_AngelDevil_Game
namespace AngelDevil

theorem jump_self (p : Nat) (v : Point) : Jump p v v := by
  unfold Jump
  omega

theorem jump_mono {p q : Nat} (hpq : p ≤ q) {u v : Point}
    (h : Jump p u v) : Jump q u v := by
  unfold Jump at *
  omega

theorem jump_symm {p : Nat} {u v : Point} (h : Jump p u v) : Jump p v u := by
  unfold Jump at *
  omega

theorem jump_add {p q : Nat} {u v w : Point}
    (h : Jump p u v) (h' : Jump q v w) : Jump (p+q) u w := by
  unfold Jump at *
  omega

theorem play_lengths (A : AngelStrategy) (D : DevilStrategy) (n : Nat) :
    (play A D n).visited.length = n+1 ∧ (play A D n).burned.length = n := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih => simp_all [play, step, List.length_append, Nat.add_assoc]

theorem pass_is_nice (p : Nat) : Nice p (fun _ => none) := by
  intro h hj z hz
  contradiction

/- Proposition 4.3's final numerical contradiction. The geometric estimates
are hypotheses here; establishing them remains open. -/
theorem wall_budget_contradiction (t d a N perimeter : Int)
    (hd : d ≤ t) (ha : 2*t-1 ≤ a)
    (hlower : a+2*N+5 ≤ perimeter)
    (hupper : perimeter ≤ 2*(N+d)+2) : False := by
  omega

theorem nice_wins_excludes_confinement {p N : Nat} (h : NiceAngelWins p) :
    ¬ NiceCanConfine p N := by
  intro hc
  obtain ⟨A, hA⟩ := h
  obtain ⟨D, hn, hD⟩ := hc
  obtain ⟨hs, he⟩ := hA D hn
  obtain ⟨n, hn'⟩ := he N
  exact hn' (hD A n (fun m _ => hs m))

/- A proved logical assembly lemma, NOT a proof of either paper milestone. -/
theorem nice_escape_and_reduction_imply_win {p : Nat}
    (reduction : ¬ AngelWins p → ∃ N, 0 < N ∧ NiceCanConfine p N)
    (escape : NiceAngelWins p) : AngelWins p := by
  apply Classical.byContradiction
  intro h
  obtain ⟨N, _, hN⟩ := reduction h
  exact nice_wins_excludes_confinement escape hN

end AngelDevil
