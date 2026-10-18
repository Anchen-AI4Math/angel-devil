import Solutions.WallStrategy

namespace AngelDevil

/-- Initial vertex of the unit segment oriented with its occupied square on the left. -/
def wallStart (w : Wall) : Point :=
  let x := w.1.1
  let y := w.1.2
  if w.2.1 then
    if w.2.2 then (x,y) else (x+1,y+1)
  else if w.2.2 then (x,y+1) else (x+1,y)

def wallEnd (w : Wall) : Point := sideNeighbor (wallStart w) (tangentSide w.2)

theorem wallStart_initial : wallStart initialWall = origin := rfl

theorem nextWall_start (B : Set Point) (w : Wall) :
    wallStart (nextWall B w) = wallEnd w := by
  classical
  unfold nextWall
  dsimp only
  split
  · rcases w with ⟨⟨x,y⟩,a,b⟩
    cases a <;> cases b <;>
      simp [wallStart, wallEnd, tangentSide, sideNeighbor]
  · split
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;>
        simp [wallStart, wallEnd, tangentSide, sideNeighbor]
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;>
        simp [wallStart, wallEnd, tangentSide, sideNeighbor, oppositeSide]

theorem wallTrace_end_start (D : DevilStrategy) (i : Nat) :
    wallEnd (wallTrace D i) = wallStart (wallTrace D (i+1)) := by
  rw [wallTrace, nextWall_start]

/-- Freezing later obstacles preserves a past transition when both outside
squares remain empty. -/
theorem nextWall_stable {B C : Set Point} (hBC : B ⊆ C) (w : Wall)
    (hnext : wallOutside (nextWall B w) ∉ C) : nextWall C w = nextWall B w := by
  classical
  unfold nextWall at *
  dsimp only at *
  split at hnext
  · rename_i ha
    change sideNeighbor w.1 (tangentSide w.2) ∉ C at hnext
    simp only [if_pos ha, if_pos hnext]
  · rename_i ha
    have haC : sideNeighbor w.1 (tangentSide w.2) ∈ C := hBC (by simpa using ha)
    split at hnext
    · rename_i hb
      change sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∉ C at hnext
      simp only [if_neg ha, if_neg (not_not.mpr haC), if_pos hb, if_pos hnext]
    · rename_i hb
      have hbC : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ C :=
        hBC (by simpa using hb)
      simp only [if_neg ha, if_neg hb, if_neg (not_not.mpr haC), if_neg (not_not.mpr hbC)]

theorem wallTrace_frozen_step (D : DevilStrategy) (hnice : Nice 2 D)
    (i j : Nat) (hij : i < j) :
    nextWall (traceObstacles D j) (wallTrace D i) = wallTrace D (i+1) := by
  rw [wallTrace]
  apply nextWall_stable (traceObstacles_monotone D (Nat.le_of_lt hij))
  change wallOutside (wallTrace D (i+1)) ∉ traceObstacles D j
  exact wallTrace_protected D hnice (i+1) j (by omega)

theorem boundary_halfplane_support {B : Set Point}
    (hleft : ∀ v : Point, v.1 < 0 → v ∈ B) {w : Wall} (hw : IsBoundaryWall B w) :
    -1 ≤ w.1.1 ∧ 0 ≤ (wallOutside w).1 := by
  have hout : 0 ≤ (wallOutside w).1 := by
    by_contra hn
    exact hw.2 (hleft _ (by omega))
  refine ⟨?_, hout⟩
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallOutside, sideNeighbor] at hout ⊢ <;> omega

theorem boundary_halfplane_start_nonneg {B : Set Point}
    (hleft : ∀ v : Point, v.1 < 0 → v ∈ B) {w : Wall} (hw : IsBoundaryWall B w) :
    0 ≤ (wallStart w).1 := by
  have hout := (boundary_halfplane_support hleft hw).2
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallOutside, sideNeighbor, wallStart] at hout ⊢ <;> omega

noncomputable def staticWall (B : Set Point) (w : Wall) : Nat → Wall
  | 0 => w
  | n+1 => nextWall B (staticWall B w n)

theorem staticWall_boundary {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w)
    (n : Nat) : IsBoundaryWall B (staticWall B w n) := by
  induction n with
  | zero => exact hw
  | succ n ih => exact nextWall_boundary ih

theorem staticWall_cancel {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w)
    {i j : Nat} (hij : i ≤ j) (heq : staticWall B w i = staticWall B w j) :
    w = staticWall B w (j-i) := by
  induction i generalizing j with
  | zero => simpa only [Nat.sub_zero, staticWall] using heq
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      have he := nextWall_injective (staticWall_boundary hw i) (staticWall_boundary hw j) heq
      simpa only [Nat.add_sub_add_right] using ih (by omega) he

theorem staticWall_mem_boundary {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) (n : Nat) :
    staticWall (s : Set Point) w n ∈ boundaryWalls s := by
  have h := staticWall_boundary hw n
  generalize staticWall (s : Set Point) w n = v at *
  rcases v with ⟨u,d⟩
  exact (mem_boundaryWalls s u d).mpr h

theorem staticWall_returns {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ n, 0 < n ∧ staticWall (s : Set Point) w n = w := by
  classical
  by_contra hreturn
  let f (n : Nat) : {v // v ∈ boundaryWalls s} :=
    ⟨staticWall (s : Set Point) w n, staticWall_mem_boundary hw n⟩
  have hf : Function.Injective f := by
    intro i j he
    have heq := congrArg Subtype.val he
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact False.elim (hreturn ⟨j-i, by omega,
        (staticWall_cancel hw (Nat.le_of_lt hlt) heq).symm⟩)
    · exact he
    · exact False.elim (hreturn ⟨i-j, by omega,
        (staticWall_cancel hw (Nat.le_of_lt hgt) heq.symm).symm⟩)
  exact Finite.false (Finite.of_injective f hf)

/-- The least positive return is a simple directed-wall cycle. -/
theorem staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧
      (∀ i j, i < L → j < L → staticWall (s : Set Point) w i =
        staticWall (s : Set Point) w j → i = j) ∧ L ≤ squarePerimeter s := by
  classical
  have hex := staticWall_returns hw
  let L := Nat.find hex
  have hL : 0 < L ∧ staticWall (s : Set Point) w L = w := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → k < L → staticWall (s : Set Point) w k ≠ w := by
    intro k hk hkL he
    have h := Nat.find_min' hex ⟨hk, he⟩
    omega
  have hi : ∀ i j, i < L → j < L → staticWall (s : Set Point) w i =
      staticWall (s : Set Point) w j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact False.elim (hmin (j-i) (by omega) (by omega)
        (staticWall_cancel hw (Nat.le_of_lt hlt) he).symm)
    · exact heq
    · exact False.elim (hmin (i-j) (by omega) (by omega)
        (staticWall_cancel hw (Nat.le_of_lt hgt) he.symm).symm)
  refine ⟨L, hL.1, hL.2, hi, ?_⟩
  have hsub : (Finset.range L).image (staticWall (s : Set Point) w) ⊆ boundaryWalls s := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact staticWall_mem_boundary hw i
  have hcard : ((Finset.range L).image (staticWall (s : Set Point) w)).card = L := by
    rw [Finset.card_image_iff.mpr]
    · exact Finset.card_range L
    · intro i hi' j hj' he
      exact hi i j (Finset.mem_range.mp hi') (Finset.mem_range.mp hj') he
  have hb := Finset.card_le_card hsub
  rw [hcard, boundaryWalls_card] at hb
  exact hb

theorem connected_staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hconn : SquaresConnected s) (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧ L ≤ 2*s.card+2 := by
  obtain ⟨L, hL, hreturn, _, hbound⟩ := staticWall_cycle_bound hw
  exact ⟨L, hL, hreturn, hbound.trans (connectedSquares_perimeter hconn)⟩

theorem staticWall_shift (B : Set Point) (w : Wall) (n : Nat) :
    staticWall B w (n+1) = staticWall B (nextWall B w) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextWall B (staticWall B w (n+1)) = nextWall B (staticWall B (nextWall B w) n)
    rw [ih]

theorem staticWall_orbit_predecessor {B : Set Point} {w v : Wall} {L : Nat}
    (hw : IsBoundaryWall B w) (hv : IsBoundaryWall B v) (hL : 0 < L)
    (hreturn : staticWall B w L = w)
    (hnext : ∃ k, k < L ∧ nextWall B v = staticWall B w k) :
    ∃ k, k < L ∧ v = staticWall B w k := by
  obtain ⟨k, hk, he⟩ := hnext
  cases k with
  | zero =>
    have hlast : nextWall B (staticWall B w (L-1)) = w := by
      have h := hreturn
      conv_lhs at h => rw [show L = (L-1)+1 by omega]
      exact h
    refine ⟨L-1, by omega, ?_⟩
    apply nextWall_injective hv (staticWall_boundary hw (L-1))
    exact he.trans hlast.symm
  | succ k =>
    exact ⟨k, by omega, nextWall_injective hv (staticWall_boundary hw k) he⟩

theorem staticWall_reaches_orbit {B : Set Point} {w v : Wall} {L : Nat}
    (hw : IsBoundaryWall B w) (hv : IsBoundaryWall B v) (hL : 0 < L)
    (hreturn : staticWall B w L = w) (m : Nat)
    (hreach : ∃ k, k < L ∧ staticWall B v m = staticWall B w k) :
    ∃ k, k < L ∧ v = staticWall B w k := by
  induction m generalizing v with
  | zero => exact hreach
  | succ m ih =>
    simp only [staticWall_shift] at hreach
    exact staticWall_orbit_predecessor hw hv hL hreturn
      (ih (nextWall_boundary hv) hreach)

theorem wall_northwest_potential (w : Wall) :
    (wallEnd w).2 - (wallEnd w).1 ≤ (wallStart w).2 - (wallStart w).1 + 1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallEnd, wallStart, sideNeighbor, tangentSide] <;> omega

theorem wall_southeast_potential (w : Wall) :
    (wallEnd w).1 - (wallEnd w).2 ≤ (wallStart w).1 - (wallStart w).2 + 1 := by
  rcases w with ⟨⟨x,y⟩,a,b⟩
  cases a <;> cases b <;> simp [wallEnd, wallStart, sideNeighbor, tangentSide] <;> omega

theorem staticWall_potential_bound (B : Set Point) (w : Wall) (f : Point → Int)
    (hf : ∀ v : Wall, f (wallEnd v) ≤ f (wallStart v) + 1)
    {i j : Nat} (hij : i ≤ j) :
    f (wallStart (staticWall B w j)) - f (wallStart (staticWall B w i)) ≤ (j-i : Nat) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hs := hf (staticWall B w j)
    have he : wallStart (staticWall B w (j+1)) = wallEnd (staticWall B w j) :=
      nextWall_start B _
    rw [he]
    omega

end AngelDevil
