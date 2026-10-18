import Solutions.WallTruncation

namespace AngelDevil

noncomputable def traceHeight (D : DevilStrategy) (j : Nat) : Nat :=
  (Finset.range (j+1)).sup (fun i => (wallTrace D i).1.2.toNat) + 3

theorem traceHeight_pos (D : DevilStrategy) (j : Nat) : 0 < traceHeight D j := by
  unfold traceHeight
  omega

theorem traceHeight_bound (D : DevilStrategy) {i j : Nat} (hij : i ≤ j) :
    (wallTrace D i).1.2 + 2 < (traceHeight D j : Int) := by
  have h := Finset.le_sup (f := fun i => (wallTrace D i).1.2.toNat)
    (Finset.mem_range.mpr (show i < j+1 by omega))
  unfold traceHeight
  omega

theorem wallStart_height (w : Wall) : (wallStart w).2 ≤ w.1.2+1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallStart]

theorem wall_tests_in_strip (w : Wall) (hx : 0 ≤ (wallOutside w).1)
    (hy : 0 ≤ (wallStart w).2) (he : 0 < (wallEnd w).2) :
    let a := sideNeighbor w.1 (tangentSide w.2)
    let b := sideNeighbor a w.2
    (-1 ≤ a.1 ∧ 0 ≤ a.2 ∧ a.2 ≤ w.1.2+1) ∧
      (-1 ≤ b.1 ∧ 0 ≤ b.2 ∧ b.2 ≤ w.1.2+1) := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;>
    simp [wallOutside, wallStart, wallEnd, sideNeighbor, tangentSide] at * <;> omega

theorem nextWall_congr_tests (B C : Set Point) (w : Wall)
    (ha : sideNeighbor w.1 (tangentSide w.2) ∈ B ↔
      sideNeighbor w.1 (tangentSide w.2) ∈ C)
    (hb : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ B ↔
      sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ C) :
    nextWall B w = nextWall C w := by
  classical
  simp only [nextWall, ha, hb]

theorem nice_origin_not_burned {D : DevilStrategy} (hnice : Nice 2 D) (n : Nat) :
    some origin ∉ (play wallAngel D n).burned := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
    have hne : D (play wallAngel D n).visited ≠ some origin := by
      intro he
      exact (hnice _ (survives_journey (wallAngel_survives_nice D hnice) n) origin he).1 rfl
    change some origin ∉ (play wallAngel D n).burned ++ [_]
    simpa using And.intro ih (Ne.symm hne)

theorem trace_frozen_prefix (D : DevilStrategy) (hnice : Nice 2 D) {j : Nat}
    (hpositive : ∀ k, 0 < k → k < j → 0 < (wallStart (wallTrace D k)).2) :
    ∀ i, i < j →
      staticWall (frozenSquares (traceHeight D j)
        (play wallAngel D ((j-1)/2+1)).burned : Set Point) initialWall i = wallTrace D i := by
  let N := traceHeight D j
  let b := (play wallAngel D ((j-1)/2+1)).burned
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hij
    change nextWall (frozenSquares N b : Set Point) (staticWall _ initialWall i) = _
    rw [ih (by omega)]
    have hw := wallTrace_boundary D hnice i
    have hx : 0 ≤ (wallOutside (wallTrace D i)).1 :=
      (boundary_halfplane_support (fun _ h => Or.inl h) hw).2
    have hy : 0 ≤ (wallStart (wallTrace D i)).2 := by
      by_cases hi : i = 0
      · subst i; exact Int.le_refl 0
      · exact le_of_lt (hpositive i (by omega) (by omega))
    have he : 0 < (wallEnd (wallTrace D i)).2 := by
      rw [wallTrace_end_start]
      exact hpositive (i+1) (by omega) hij
    have ht := wall_tests_in_strip (wallTrace D i) hx hy he
    have hheight := traceHeight_bound D (show i ≤ j by omega)
    have heq : nextWall (frozenSquares N b : Set Point) (wallTrace D i) =
        nextWall (traceObstacles D (j-1)) (wallTrace D i) := by
      apply nextWall_congr_tests
      · exact frozenSquares_agree N b _ ht.1.1 ht.1.2.1 (by dsimp [N]; omega)
      · exact frozenSquares_agree N b _ ht.2.1 ht.2.2.1 (by dsimp [N]; omega)
    rw [heq]
    exact wallTrace_frozen_step D hnice i (j-1) (by omega)

theorem wall_down_to_axis (w : Wall) (hx : 0 ≤ (wallOutside w).1)
    (hy : 0 < (wallStart w).2) (he : (wallEnd w).2 ≤ 0) :
    ∃ x : Int, 1 ≤ x ∧ w = ((x,0),(false,true)) := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;>
    simp [wallOutside, wallStart, wallEnd, sideNeighbor, tangentSide] at hx hy he ⊢
  all_goals omega

theorem wallTrace_no_first_axis_contact (D : DevilStrategy) (hnice : Nice 2 D)
    {j : Nat} (hj : 0 < j)
    (hpositive : ∀ k, 0 < k → k < j → 0 < (wallStart (wallTrace D k)).2)
    (hcontact : (wallStart (wallTrace D j)).2 ≤ 0) : False := by
  have hone : wallStart (wallTrace D 1) = (0,1) := by
    rw [← wallTrace_end_start D 0]
    rfl
  have hj2 : 1 < j := by
    by_contra h
    have hjeq : j = 1 := by omega
    rw [hjeq, hone] at hcontact
    dsimp at hcontact
    omega
  let N := traceHeight D j
  let t := (j-1)/2+1
  let b := (play wallAngel D t).burned
  let B : Set Point := frozenSquares N b
  have hN : 0 < N := traceHeight_pos D j
  have hclear : some origin ∉ b := nice_origin_not_burned hnice t
  have hbefore := hpositive (j-1) (by omega) (by omega)
  have hend : (wallEnd (wallTrace D (j-1))).2 ≤ 0 := by
    rw [wallTrace_end_start, show j-1+1 = j by omega]
    exact hcontact
  have hout : 0 ≤ (wallOutside (wallTrace D (j-1))).1 :=
    (boundary_halfplane_support (fun _ h => Or.inl h) (wallTrace_boundary D hnice (j-1))).2
  obtain ⟨x, hx, hwall⟩ := wall_down_to_axis (wallTrace D (j-1)) hout hbefore hend
  have hpast : staticWall B initialWall (j-1) = wallTrace D (j-1) :=
    trace_frozen_prefix D hnice hpositive (j-1) (by omega)
  have hjwall : staticWall B initialWall j = ((x,0),(true,true)) := by
    conv_lhs => rw [show j = (j-1)+1 by omega]
    change nextWall B (staticWall B initialWall (j-1)) = _
    rw [hpast, hwall]
    simp [B, nextWall, tangentSide, sideNeighbor, mem_frozenSquares]
  have heast : wallStart (staticWall B initialWall (j+1)) = (x+1,0) := by
    change wallStart (nextWall B (staticWall B initialWall j)) = _
    rw [nextWall_start, hjwall]
    simp [wallEnd, wallStart, tangentSide, sideNeighbor]
  have hprefix : ∀ i, i ≤ j → (wallStart (staticWall B initialWall i)).2 < (N : Int) := by
    intro i hij
    by_cases heq : i = j
    · subst i
      rw [hjwall]
      simp only [wallStart]
      dsimp
      omega
    · have hi : i < j := by omega
      rw [trace_frozen_prefix D hnice hpositive i hi]
      have ht := traceHeight_bound D hij
      have hs := wallStart_height (wallTrace D i)
      dsimp [N]
      omega
  obtain ⟨L, hL, hreturn, hupper⟩ := frozenSquares_cycle_budget hN hclear
  have hlower := frozenSquares_return_lower hN hclear hL hreturn x hx heast hprefix
  have hlen : b.length = t := (play_lengths wallAngel D t).2
  have hbudget : 2*t-1 ≤ j := by dsimp [t]; omega
  omega

theorem wallTrace_above_axis (D : DevilStrategy) (hnice : Nice 2 D)
    (n : Nat) (hn : 0 < n) : 0 < (wallStart (wallTrace D n)).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_contra h
    exact wallTrace_no_first_axis_contact D hnice hn
      (fun k hk hkn => ih k hkn hk) (by omega)

theorem wallTrace_never_returns (D : DevilStrategy) (hnice : Nice 2 D)
    (n : Nat) (hn : 0 < n) : wallTrace D n ≠ initialWall := by
  intro heq
  have h := wallTrace_above_axis D hnice n hn
  rw [heq, wallStart_initial] at h
  change 0 < (0 : Int) at h
  omega

end AngelDevil
