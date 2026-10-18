import Solutions.WallWalk
import Solutions.Histories

namespace AngelDevil

theorem wallHistory_nil : wallHistory [] = initialWall := by
  rw [wallHistory]
  simp

theorem wallHistory_append (b : List (Option Point)) (d : Option Point) :
    wallHistory (b ++ [d]) =
      nextWall (wallObstacles (b ++ [d]))
        (nextWall (wallObstacles (b ++ [d])) (wallHistory b)) := by
  rw [wallHistory]
  simp

theorem wall_current (D : DevilStrategy) (n : Nat) :
    current (play wallAngel D n) = wallOutside (wallHistory (play wallAngel D n).burned) := by
  cases n with
  | zero => simp [play, initial, current, wallHistory_nil, initialWall, wallOutside, sideNeighbor, origin]
  | succ n => rw [current_succ]; rfl

theorem wallObstacles_mono {b c : List (Option Point)} (h : ∀ x ∈ b, x ∈ c) :
    wallObstacles b ⊆ wallObstacles c := by
  intro v hv
  rcases hv with hv | hv
  · exact Or.inl hv
  · exact Or.inr (h _ hv)

theorem wall_play_invariant (D : DevilStrategy) (hnice : Nice 2 D) (n : Nat) :
    IsBoundaryWall (wallObstacles (play wallAngel D n).burned)
      (wallHistory (play wallAngel D n).burned) ∧
    ∀ m, m < n → Jump 2 (current (play wallAngel D m))
      (current (play wallAngel D (m+1))) := by
  induction n with
  | zero =>
    constructor
    · simp [play, initial, wallHistory_nil, IsBoundaryWall, initialWall,
        wallOutside, sideNeighbor, wallObstacles]
    · intro m hm
      omega
  | succ n ih =>
    let b := (play wallAngel D n).burned
    let d := D (play wallAngel D n).visited
    have hnot : d ≠ some (wallOutside (wallHistory b)) := by
      simpa only [wall_current] using nice_does_not_eat_current 2 wallAngel D hnice n ih.2
    have hext : wallObstacles b ⊆ wallObstacles (b ++ [d]) :=
      wallObstacles_mono (fun x hx => List.mem_append_left _ hx)
    have hbefore : IsBoundaryWall (wallObstacles (b ++ [d])) (wallHistory b) := by
      refine ⟨hext ih.1.1, ?_⟩
      intro heaten
      rcases heaten with hleft | hburn
      · exact ih.1.2 (Or.inl hleft)
      · rcases List.mem_append.mp hburn with hprior | hlast
        · exact ih.1.2 (Or.inr hprior)
        · exact hnot (List.mem_singleton.mp hlast).symm
    have htwo := two_wall_steps_legal hbefore
    have hboundary : IsBoundaryWall (wallObstacles (play wallAngel D (n+1)).burned)
        (wallHistory (play wallAngel D (n+1)).burned) := by
      simpa only [play, step, wallHistory_append] using htwo.1
    have hjump : Jump 2 (current (play wallAngel D n))
        (current (play wallAngel D (n+1))) := by
      rw [wall_current, wall_current]
      change Jump 2 (wallOutside (wallHistory b)) (wallOutside (wallHistory (b ++ [d])))
      rw [wallHistory_append]
      exact htwo.2
    refine ⟨hboundary, ?_⟩
    intro m hm
    by_cases hmn : m = n
    · simpa only [hmn] using hjump
    · exact ih.2 m (by omega)

theorem wallAngel_survives_nice (D : DevilStrategy) (hnice : Nice 2 D) :
    Survives 2 wallAngel D := by
  intro n
  have h := wall_play_invariant D hnice (n+1)
  refine ⟨h.2 n (by omega), ?_⟩
  rw [wall_current]
  exact fun hb => h.1.2 (Or.inr hb)

theorem play_burned_mono (A : AngelStrategy) (D : DevilStrategy) {n m : Nat}
    (hnm : n ≤ m) : ∀ x ∈ (play A D n).burned, x ∈ (play A D m).burned := by
  induction m, hnm using Nat.le_induction with
  | base => exact fun _ h => h
  | succ m _ ih =>
    intro x hx
    exact List.mem_append_left _ (ih x hx)

theorem nice_neighborhood_persistent {p : Nat} {A : AngelStrategy} {D : DevilStrategy}
    (hnice : Nice p D) (hsafe : Survives p A D) (n : Nat) (z : Point)
    (hjump : Jump p (current (play A D n)) z)
    (hclear : some z ∉ (play A D (n+1)).burned) :
    ∀ m, n+1 ≤ m → some z ∉ (play A D m).burned := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hclear
  | succ m hnm ih =>
    have hne : D (play A D m).visited ≠ some z := by
      intro he
      have hp := (hnice _ (survives_journey hsafe m) z he).2
      have hmem : current (play A D n) ∈ (play A D m).visited.dropLast := by
        cases m with
        | zero => omega
        | succ k =>
          simpa only [play, step, List.dropLast_concat] using
            List.mem_of_getElem? (visited_get A D k n (by omega))
      exact hp _ hmem hjump
    intro he
    change some z ∈ (play A D m).burned ++ [D (play A D m).visited] at he
    rcases List.mem_append.mp he with hold | hlast
    · exact ih hold
    · exact hne (List.mem_singleton.mp hlast).symm

theorem wall_before_turn (D : DevilStrategy) (hnice : Nice 2 D) (n : Nat) :
    IsBoundaryWall (wallObstacles (play wallAngel D (n+1)).burned)
      (wallHistory (play wallAngel D n).burned) := by
  have hi := wall_play_invariant D hnice n
  have hne := nice_does_not_eat_current 2 wallAngel D hnice n hi.2
  rw [wall_current] at hne
  constructor
  · exact wallObstacles_mono (play_burned_mono wallAngel D (Nat.le_succ n)) hi.1.1
  · intro he
    rcases he with hleft | hburn
    · exact hi.1.2 (Or.inl hleft)
    · change some _ ∈ (play wallAngel D n).burned ++ [_] at hburn
      rcases List.mem_append.mp hburn with hold | hlast
      · exact hi.1.2 (Or.inr hold)
      · exact hne (List.mem_singleton.mp hlast).symm

theorem traceObstacles_even (D : DevilStrategy) (n : Nat) :
    traceObstacles D (2*n) = wallObstacles (play wallAngel D (n+1)).burned := by
  unfold traceObstacles
  congr 3; omega

theorem traceObstacles_odd (D : DevilStrategy) (n : Nat) :
    traceObstacles D (2*n+1) = wallObstacles (play wallAngel D (n+1)).burned := by
  unfold traceObstacles
  congr 3; omega

theorem wallTrace_even (D : DevilStrategy) (n : Nat) :
    wallTrace D (2*n) = wallHistory (play wallAngel D n).burned := by
  induction n with
  | zero => simp [wallTrace, play, initial, wallHistory_nil]
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, wallTrace, wallTrace,
      traceObstacles_odd, traceObstacles_even, ih]
    change _ = wallHistory ((play wallAngel D n).burned ++ [_])
    rw [wallHistory_append]
    rfl

theorem wallTrace_odd (D : DevilStrategy) (n : Nat) :
    wallTrace D (2*n+1) = nextWall (wallObstacles (play wallAngel D (n+1)).burned)
      (wallHistory (play wallAngel D n).burned) := by
  rw [wallTrace, traceObstacles_even, wallTrace_even]

theorem wallTrace_boundary (D : DevilStrategy) (hnice : Nice 2 D) (i : Nat) :
    IsBoundaryWall (traceObstacles D i) (wallTrace D i) := by
  have hcases : ∃ n, i = 2*n ∨ i = 2*n+1 := ⟨i/2, by omega⟩
  obtain ⟨n, h | h⟩ := hcases
  · subst i
    rw [traceObstacles_even, wallTrace_even]
    exact wall_before_turn D hnice n
  · subst i
    rw [traceObstacles_odd, wallTrace_odd]
    exact nextWall_boundary (wall_before_turn D hnice n)

theorem wallTrace_near_round (D : DevilStrategy) (i : Nat) :
    Jump 2 (current (play wallAngel D (i/2))) (wallOutside (wallTrace D i)) := by
  have hcases : ∃ n, i = 2*n ∨ i = 2*n+1 := ⟨i/2, by omega⟩
  obtain ⟨n, h | h⟩ := hcases
  · subst i
    rw [show 2*n/2 = n by omega, wallTrace_even, wall_current]
    exact jump_self 2 _
  · subst i
    rw [show (2*n+1)/2 = n by omega, wallTrace_odd, wall_current]
    exact jump_mono (by omega) (nextWall_jump _)

theorem traceObstacles_monotone (D : DevilStrategy) : Monotone (traceObstacles D) := by
  intro i j hij
  exact wallObstacles_mono (play_burned_mono wallAngel D (by omega))

theorem wallTrace_protected (D : DevilStrategy) (hnice : Nice 2 D)
    (i j : Nat) (hij : i ≤ j) : wallOutside (wallTrace D i) ∉ traceObstacles D j := by
  have hc := (wallTrace_boundary D hnice i).2
  have hp := nice_neighborhood_persistent hnice (wallAngel_survives_nice D hnice)
    (i/2) (wallOutside (wallTrace D i)) (wallTrace_near_round D i)
    (fun hb => hc (Or.inr hb)) (j/2+1) (by omega)
  intro he
  rcases he with hleft | hburn
  · exact hc (Or.inl hleft)
  · exact hp hburn

theorem wallTrace_first_repeat (D : DevilStrategy) (hnice : Nice 2 D)
    {i j : Nat} (hij : i < j) (heq : wallTrace D i = wallTrace D j)
    (hinj : ∀ a b, a < j → b < j → wallTrace D a = wallTrace D b → a = b) :
    i = 0 :=
  first_wall_repeat_is_initial (traceObstacles D) (wallTrace D)
    (traceObstacles_monotone D) (wallTrace_boundary D hnice) (fun _ => rfl)
    (wallTrace_protected D hnice) hij heq hinj

theorem wallTrace_injective_of_no_return (D : DevilStrategy) (hnice : Nice 2 D)
    (hreturn : ∀ n, 0 < n → wallTrace D n ≠ initialWall) :
    Function.Injective (wallTrace D) := by
  have distinct : ∀ j i, i < j → wallTrace D i ≠ wallTrace D j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro i hij heq
      have hfirst := wallTrace_first_repeat D hnice hij heq (by
        intro a b ha hb hab
        rcases lt_trichotomy a b with hlt | he | hgt
        · exact False.elim (ih b hb a hlt hab)
        · exact he
        · exact False.elim (ih a ha b hgt hab.symm))
      subst i
      exact hreturn j (by omega) heq.symm
  intro i j heq
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact False.elim (distinct j i hlt heq)
  · exact he
  · exact False.elim (distinct i j hgt heq.symm)

def boxCode (N : Nat) (v : Point) (h : InBox N v) : Fin (2*N+1) × Fin (2*N+1) :=
  (⟨(v.1 + N).toNat, by unfold InBox Jump origin at h; dsimp at h; omega⟩,
   ⟨(v.2 + N).toNat, by unfold InBox Jump origin at h; dsimp at h; omega⟩)

theorem boxCode_injective {N : Nat} {u v : Point} (hu : InBox N u) (hv : InBox N v)
    (heq : boxCode N u hu = boxCode N v hv) : u = v := by
  have hx := congrArg (fun c => c.1.val) heq
  have hy := congrArg (fun c => c.2.val) heq
  unfold boxCode at hx hy
  dsimp only at hx hy
  unfold InBox Jump origin at hu hv
  apply Prod.ext <;> omega

theorem wallAngel_escapes_of_no_return (D : DevilStrategy) (hnice : Nice 2 D)
    (hreturn : ∀ n, 0 < n → wallTrace D n ≠ initialWall) : Escapes wallAngel D := by
  classical
  intro N
  by_contra hbound
  have hb : ∀ n, InBox N (current (play wallAngel D n)) := by simpa using hbound
  have ht : ∀ i, InBox (N+2) (wallOutside (wallTrace D i)) := by
    intro i
    exact jump_add (hb (i/2)) (wallTrace_near_round D i)
  let code (i : Nat) : (Fin (2*(N+2)+1) × Fin (2*(N+2)+1)) × SquareSide :=
    (boxCode (N+2) (wallOutside (wallTrace D i)) (ht i), (wallTrace D i).2)
  have hc : Function.Injective code := by
    intro i j he
    apply wallTrace_injective_of_no_return D hnice hreturn
    apply wall_determined_by_outside_normal
    · exact boxCode_injective (ht i) (ht j) (congrArg Prod.fst he)
    · exact (congrArg Prod.snd he : (code i).2 = (code j).2)
  exact Finite.false (Finite.of_injective code hc)

/-- The remaining geometric no-return obligation suffices for the original
Nice-Angel target with its single strategy and universal Devil quantifier. -/
theorem niceAngelWins_of_wall_no_return
    (hreturn : ∀ D, Nice 2 D → ∀ n, 0 < n → wallTrace D n ≠ initialWall) :
    NiceAngelWins 2 := by
  refine ⟨wallAngel, ?_⟩
  intro D hnice
  exact ⟨wallAngel_survives_nice D hnice,
    wallAngel_escapes_of_no_return D hnice (hreturn D hnice)⟩

end AngelDevil
