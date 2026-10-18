import Definitions.Def_AngelDevil_FiniteGame
import Solutions.StrategyCompactness

namespace AngelDevil

theorem finiteAngel_spec (p T : Nat) (s : State) (d : Option Point)
    (hv : Viable p (T-s.visited.length+1) s) :
    let v := finiteAngel p T s.visited (s.burned ++ [d])
    Jump p (current s) v ∧ some v ∉ s.burned ++ [d] ∧
      Viable p (T-s.visited.length) (advance s d v) := by
  have hex := hv d
  unfold finiteAngel
  simp only [current, advance] at hex ⊢
  simp only [hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem viable_has_strategy (p T : Nat) (hv : Viable p T initial) :
    FiniteAngelWins p T := by
  refine ⟨finiteAngel p T, ?_⟩
  intro D
  let A := finiteAngel p T
  have inv : ∀ n, n ≤ T → SafeFor p A D n ∧ Viable p (T-n) (play A D n) := by
    intro n
    induction n with
    | zero =>
        intro _
        exact ⟨fun m hm => by omega, by simpa only [Nat.sub_zero, play] using hv⟩
    | succ n ih =>
        intro hn
        obtain ⟨hs, hvi⟩ := ih (by omega)
        have hlen := (play_lengths A D n).1
        have hr : T-n = T-(play A D n).visited.length+1 := by omega
        rw [hr] at hvi
        have hc := finiteAngel_spec p T (play A D n) (D (play A D n).visited) hvi
        have hstep : Jump p (current (play A D n)) (current (play A D (n+1))) ∧
            some (current (play A D (n+1))) ∉ (play A D (n+1)).burned := by
          rw [current_succ]
          exact ⟨hc.1, hc.2.1⟩
        constructor
        · intro m hm
          by_cases hmn : m < n
          · exact hs m hmn
          · have : m = n := by omega
            subst m
            exact hstep
        · simpa only [hlen, play, step, advance, A] using hc.2.2
  exact (inv T (by omega)).1

theorem badMove_spec (p n : Nat) (s : State) (hn : ¬ Viable p (n+1) s) :
    ∀ v, Jump p (current s) v → some v ∉ s.burned ++ [badMove p n s] →
      ¬ Viable p n (advance s (badMove p n s) v) := by
  classical
  have hex : ∃ d : Option Point, ∀ v, Jump p (current s) v →
      some v ∉ s.burned ++ [d] → ¬ Viable p n (advance s d v) := by
    by_contra hh
    apply hn
    intro d
    by_contra hd
    exact hh ⟨d, fun v hj hb hv => hd ⟨v, hj, hb, hv⟩⟩
  simp only [badMove, hex, ↓reduceDIte]
  exact Classical.choose_spec hex

theorem simulatedBurns_append (choose : State → Option Point) (h : List Point)
    (hne : h ≠ []) (v : Point) :
    simulatedBurns choose (h ++ [v]) =
      simulatedBurns choose h ++ [choose ⟨h, simulatedBurns choose h⟩] := by
  rw [simulatedBurns]
  simp [hne]

theorem simulatedBurns_play (choose : State → Option Point) (A : AngelStrategy)
    (n : Nat) : simulatedBurns choose (play A (historyDevil choose) n).visited =
      (play A (historyDevil choose) n).burned := by
  induction n with
  | zero => simp [play, initial, simulatedBurns]
  | succ n ih =>
      change simulatedBurns choose ((play A (historyDevil choose) n).visited ++ [_]) = _
      have hne : (play A (historyDevil choose) n).visited ≠ [] := by
        have := (play_lengths A (historyDevil choose) n).1
        intro hh
        simp [hh] at this
      rw [simulatedBurns_append choose _ hne]
      change _ = (play A (historyDevil choose) n).burned ++
        [choose ⟨(play A (historyDevil choose) n).visited,
          simulatedBurns choose (play A (historyDevil choose) n).visited⟩]
      rw [ih]

theorem historyDevil_at_play (choose : State → Option Point) (A : AngelStrategy)
    (n : Nat) : historyDevil choose (play A (historyDevil choose) n).visited =
      choose (play A (historyDevil choose) n) := by
  change choose ⟨(play A (historyDevil choose) n).visited,
    simulatedBurns choose (play A (historyDevil choose) n).visited⟩ = _
  rw [simulatedBurns_play]

theorem not_viable_forces_failure (p T : Nat) (hv : ¬ Viable p T initial) :
    ∀ A, ¬ SafeFor p A (finiteDevil p T) T := by
  intro A hs
  let D := finiteDevil p T
  have inv : ∀ n, n ≤ T → SafeFor p A D n →
      ¬ Viable p (T-n) (play A D n) := by
    intro n
    induction n with
    | zero =>
        intro _ _
        simpa only [Nat.sub_zero, play] using hv
    | succ n ih =>
        intro hn hsafe
        have hprev := ih (by omega) (safeFor_mono p A D (n+1) n (by omega) hsafe)
        have hlen := (play_lengths A D n).1
        have hr : T-n = T-(play A D n).visited.length+1 := by omega
        rw [hr] at hprev
        have hc := badMove_spec p (T-(play A D n).visited.length) (play A D n) hprev
        have hd : D (play A D n).visited =
            badMove p (T-(play A D n).visited.length) (play A D n) :=
          historyDevil_at_play (fun s => badMove p (T-s.visited.length) s) A n
        rw [← hd] at hc
        have hstep := hsafe n (by omega)
        rw [current_succ] at hstep
        have hnxt := hc _ hstep.1 hstep.2
        simpa only [hlen, play, step, advance] using hnxt
  have hh := inv T (by omega) hs
  simp only [Nat.sub_self, Viable, not_true_eq_false] at hh

theorem finite_game_determined (p T : Nat) :
    FiniteAngelWins p T ∨ ∃ D, ∀ A, ¬ SafeFor p A D T := by
  classical
  by_cases hv : Viable p T initial
  · exact Or.inl (viable_has_strategy p T hv)
  · exact Or.inr ⟨finiteDevil p T, not_viable_forces_failure p T hv⟩

/- Exact original platform target: Claim 2.1 plus the determinacy observation. -/
theorem uniform_confinement (p : Nat) (_hp : 0 < p) (h : ¬ AngelWins p) :
    ∃ N, 0 < N ∧ ∃ D : DevilStrategy,
    ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n)) := by
  obtain ⟨T, hT⟩ := no_win_has_finite_obstruction p h
  rcases finite_game_determined p T with hw | ⟨D, hD⟩
  · exact False.elim (hT hw)
  · exact ⟨T*p+1, by omega, D, bounded_failure_confines p T D hD⟩

theorem nice_devil_reduction (p : Nat) (hp : 0 < p) :
    ¬ AngelWins p → ∃ N, 0 < N ∧ NiceCanConfine p N := by
  intro h
  obtain ⟨N, hN, D, hD⟩ := uniform_confinement p hp h
  exact ⟨N, hN, confinement_to_nice p N D hD⟩

end AngelDevil
