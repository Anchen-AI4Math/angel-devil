import Solutions.Foundation

namespace AngelDevil

theorem current_zero (A : AngelStrategy) (D : DevilStrategy) :
    current (play A D 0) = origin := rfl

theorem current_succ (A : AngelStrategy) (D : DevilStrategy) (n : Nat) :
    current (play A D (n+1)) =
      A (play A D n).visited ((play A D n).burned ++ [D (play A D n).visited]) := by
  simp [play, step, current]

theorem visited_get (A : AngelStrategy) (D : DevilStrategy) (n i : Nat)
    (hi : i ≤ n) :
    (play A D n).visited[i]? = some (current (play A D i)) := by
  induction n with
  | zero =>
      have : i = 0 := by omega
      subst i
      rfl
  | succ n ih =>
      by_cases hin : i ≤ n
      · change ((play A D n).visited ++ [_])[i]? = _
        rw [List.getElem?_append_left (by have := (play_lengths A D n).1; omega)]
        exact ih hin
      · have : i = n+1 := by omega
        subst i
        change ((play A D n).visited ++ [_])[n+1]? = _
        rw [List.getElem?_append_right (by rw [(play_lengths A D n).1]; omega)]
        simp [(play_lengths A D n).1, current_succ]

theorem safe_prefix_journey (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (safe : ∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1)))) :
    Journey p (play A D n).visited := by
  constructor
  · have h := visited_get A D n 0 (Nat.zero_le n)
    simpa only [List.head?_eq_getElem?, current_zero] using h
  · intro i u v hu hv
    have hiv := (List.getElem?_eq_some_iff.mp hv).1
    have hil : i+1 < (play A D n).visited.length := hiv
    rw [(play_lengths A D n).1] at hil
    have hi : i < n := by omega
    rw [visited_get A D n i (by omega)] at hu
    rw [visited_get A D n (i+1) (by omega)] at hv
    cases hu
    cases hv
    exact safe i hi

theorem survives_journey {p : Nat} {A : AngelStrategy} {D : DevilStrategy}
    (safe : Survives p A D) (n : Nat) : Journey p (play A D n).visited :=
  safe_prefix_journey p A D n (fun m _ => (safe m).1)

theorem nice_does_not_eat_current (p : Nat) (A : AngelStrategy)
    (D : DevilStrategy) (nice : Nice p D) (n : Nat)
    (safe : ∀ m, m < n → Jump p (current (play A D m)) (current (play A D (m+1)))) :
    D (play A D n).visited ≠ some (current (play A D n)) := by
  intro eaten
  have hprotected := nice _ (safe_prefix_journey p A D n safe) _ eaten
  cases n with
  | zero => exact hprotected.1 rfl
  | succ n =>
      have mem : current (play A D n) ∈ (play A D (n+1)).visited.dropLast := by
        simpa [play, step] using List.mem_of_getElem? (visited_get A D n n (by omega))
      exact hprotected.2 _ mem (safe n (by omega))

def stationary : AngelStrategy := fun _ _ => origin

theorem stationary_current (D : DevilStrategy) (n : Nat) :
    current (play stationary D n) = origin := by
  cases n with
  | zero => rfl
  | succ n => simp [current_succ, stationary]

theorem stationary_journey (p : Nat) (D : DevilStrategy) (n : Nat) :
    Journey p (play stationary D n).visited := by
  apply safe_prefix_journey
  intro m hm
  simp only [stationary_current]
  exact jump_self p origin

theorem stationary_not_burned (p : Nat) (D : DevilStrategy) (nice : Nice p D)
    (n : Nat) : some origin ∉ (play stationary D n).burned := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
      have h : D (play stationary D n).visited ≠ some origin := by
        intro e
        exact (nice _ (stationary_journey p D n) origin e).1 rfl
      simpa [play, step] using And.intro ih (Ne.symm h)

/- The source explicitly distinguishes survival from escape against Nice Devils:
staying at the origin survives, but is not the Theorem 4.5 target. -/
theorem stationary_survives_nice (p : Nat) (D : DevilStrategy) (nice : Nice p D) :
    Survives p stationary D := by
  intro n
  simp only [stationary_current]
  exact ⟨jump_self p origin, stationary_not_burned p D nice (n+1)⟩

theorem stationary_does_not_escape (D : DevilStrategy) : ¬ Escapes stationary D := by
  intro h
  obtain ⟨n, hn⟩ := h 0
  apply hn
  simp only [stationary_current, InBox]
  exact jump_self 0 origin

end AngelDevil
