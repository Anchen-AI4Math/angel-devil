import Solutions.WallComponent

namespace AngelDevil

def preColumn (N : Nat) : Finset Point :=
  (Finset.range N).image (fun k : Nat => ((-1 : Int), (k : Int)))

def quadrantBurns (b : List (Option Point)) : Finset Point :=
  (b.filterMap id).toFinset.filter (fun v => 0 ≤ v.1 ∧ 0 ≤ v.2)

def frozenSquares (N : Nat) (b : List (Option Point)) : Finset Point :=
  preColumn N ∪ quadrantBurns b

theorem mem_preColumn (N : Nat) (v : Point) :
    v ∈ preColumn N ↔ v.1 = -1 ∧ 0 ≤ v.2 ∧ v.2 < (N : Int) := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have hkN := Finset.mem_range.mp hk
    exact ⟨rfl, by omega, by omega⟩
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨v.2.toNat, Finset.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem mem_quadrantBurns (b : List (Option Point)) (v : Point) :
    v ∈ quadrantBurns b ↔ 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ some v ∈ b := by
  simp [quadrantBurns, List.mem_filterMap, and_comm, and_assoc]

theorem mem_frozenSquares (N : Nat) (b : List (Option Point)) (v : Point) :
    v ∈ frozenSquares N b ↔
      (v.1 = -1 ∧ 0 ≤ v.2 ∧ v.2 < (N : Int)) ∨
      (0 ≤ v.1 ∧ 0 ≤ v.2 ∧ some v ∈ b) := by
  simp only [frozenSquares, Finset.mem_union, mem_preColumn, mem_quadrantBurns]

theorem frozenSquares_card (N : Nat) (b : List (Option Point)) :
    (frozenSquares N b).card ≤ N + b.length := by
  have hcol : (preColumn N).card ≤ N := by
    have h := Finset.card_image_le (s := Finset.range N)
      (f := fun k => ((-1 : Int), (k : Int)))
    simpa only [preColumn, Finset.card_range] using h
  have hburn : (quadrantBurns b).card ≤ b.length :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le _).trans (List.length_filterMap_le id b))
  have h := Finset.card_union_le (preColumn N) (quadrantBurns b)
  unfold frozenSquares
  omega

theorem frozenSquares_agree (N : Nat) (b : List (Option Point)) (v : Point)
    (hx : -1 ≤ v.1) (hy : 0 ≤ v.2) (hN : v.2 < (N : Int)) :
    v ∈ frozenSquares N b ↔ v ∈ wallObstacles b := by
  rw [mem_frozenSquares]
  change _ ↔ v.1 < 0 ∨ some v ∈ b
  constructor
  · rintro (h | h)
    · exact Or.inl (by omega)
    · exact Or.inr h.2.2
  · rintro (h | h)
    · exact Or.inl ⟨by omega, hy, hN⟩
    · by_cases hv : v.1 < 0
      · exact Or.inl ⟨by omega, hy, hN⟩
      · exact Or.inr ⟨by omega, hy, h⟩

theorem frozenSquares_nonnegative_y {N : Nat} {b : List (Option Point)} {v : Point}
    (hv : v ∈ frozenSquares N b) : 0 ≤ v.2 := by
  rcases (mem_frozenSquares N b v).mp hv with h | h <;> exact h.2.1

theorem frozenSquares_left_bound {N : Nat} {b : List (Option Point)} {v : Point}
    (hv : v ∈ frozenSquares N b) : -1 ≤ v.1 := by
  rcases (mem_frozenSquares N b v).mp hv with h | h <;> omega

theorem frozenSquares_height {N : Nat} {b : List (Option Point)}
    (htall : ∀ v, some v ∈ b → v.2 < (N : Int)) {v : Point}
    (hv : v ∈ frozenSquares N b) : v.2 < (N : Int) := by
  rcases (mem_frozenSquares N b v).mp hv with h | h
  · exact h.2.2
  · exact htall v h.2.2

theorem frozenSquares_initial_boundary {N : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) :
    IsBoundaryWall (frozenSquares N b : Set Point) initialWall := by
  constructor
  · apply (mem_frozenSquares N b (-1,0)).mpr
    exact Or.inl ⟨rfl, by omega, by omega⟩
  · change origin ∉ frozenSquares N b
    rw [mem_frozenSquares]
    simp [origin] at hclear ⊢
    exact hclear

theorem frozenSquares_cycle_budget {N : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) :
    ∃ L, 0 < L ∧ staticWall (frozenSquares N b : Set Point) initialWall L = initialWall ∧
      L ≤ 2*(N+b.length)+2 := by
  obtain ⟨L, hL, heq, hb⟩ := finite_staticWall_cycle_bound
    (frozenSquares_initial_boundary hN hclear)
  have hc := frozenSquares_card N b
  exact ⟨L, hL, heq, by omega⟩

def columnWest (k : Nat) : Wall := ((-1, (k : Int)), (false, true))
def columnBottom : Wall := ((-1,0), (true,true))
def columnTop (N : Nat) : Wall := ((-1, (N : Int)-1), (true,false))

theorem columnWest_zero_next (N : Nat) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnWest 0) = columnBottom := by
  simp [nextWall, columnWest, columnBottom, tangentSide, sideNeighbor,
    mem_frozenSquares]

theorem columnWest_succ_next (N k : Nat) (hk : k < N) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnWest (k+1)) = columnWest k := by
  have hcol : ((-1, (k : Int)) : Point) ∈ frozenSquares N b :=
    (mem_frozenSquares N b _).mpr (Or.inl ⟨rfl, by omega, by omega⟩)
  have hout : ((-2, (k : Int)) : Point) ∉ frozenSquares N b := by
    simp [mem_frozenSquares]
  simp [nextWall, columnWest, tangentSide, sideNeighbor, hcol, hout]

theorem columnBottom_next (N : Nat) (b : List (Option Point))
    (hclear : some origin ∉ b) :
    nextWall (frozenSquares N b : Set Point) columnBottom = initialWall := by
  have h : ((0,0) : Point) ∉ frozenSquares N b := by
    have hc : some ((0,0) : Point) ∉ b := hclear
    simp [mem_frozenSquares, hc]
  simp [nextWall, columnBottom, initialWall, tangentSide, sideNeighbor, h]

theorem columnTop_next (N : Nat) (hN : 0 < N) (b : List (Option Point)) :
    nextWall (frozenSquares N b : Set Point) (columnTop N) = columnWest (N-1) := by
  have h : ((-2, (N : Int)-1) : Point) ∉ frozenSquares N b := by
    simp [mem_frozenSquares]
  have hc : ((N-1 : Nat) : Int) = (N : Int)-1 := by omega
  simp [nextWall, columnTop, columnWest, tangentSide, sideNeighbor, h, hc]

theorem columnTop_boundary (N : Nat) (hN : 0 < N) (b : List (Option Point)) :
    IsBoundaryWall (frozenSquares N b : Set Point) (columnTop N) := by
  constructor
  · apply (mem_frozenSquares N b _).mpr
    exact Or.inl ⟨rfl, by dsimp [columnTop]; omega, by dsimp [columnTop]; omega⟩
  · simp [wallOutside, columnTop, sideNeighbor, mem_frozenSquares]

theorem columnWest_reaches_initial (N k : Nat) (hk : k < N)
    (b : List (Option Point)) (hclear : some origin ∉ b) :
    staticWall (frozenSquares N b : Set Point) (columnWest k) (k+2) = initialWall := by
  induction k with
  | zero =>
    rw [staticWall_shift, columnWest_zero_next]
    exact columnBottom_next N b hclear
  | succ k ih =>
    rw [show k+1+2 = (k+2)+1 by omega, staticWall_shift, columnWest_succ_next N k (by omega)]
    exact ih (by omega)

theorem columnTop_reaches_initial (N : Nat) (hN : 0 < N)
    (b : List (Option Point)) (hclear : some origin ∉ b) :
    staticWall (frozenSquares N b : Set Point) (columnTop N) (N+2) = initialWall := by
  rw [show N+2 = ((N-1)+2)+1 by omega, staticWall_shift, columnTop_next N hN]
  exact columnWest_reaches_initial N (N-1) (by omega) b hclear

theorem columnTop_in_initial_cycle {N L : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) (hL : 0 < L)
    (hreturn : staticWall (frozenSquares N b : Set Point) initialWall L = initialWall) :
    ∃ k, k < L ∧ staticWall (frozenSquares N b : Set Point) initialWall k = columnTop N := by
  obtain ⟨k, hk, he⟩ := staticWall_reaches_orbit
    (frozenSquares_initial_boundary hN hclear) (columnTop_boundary N hN b)
    hL hreturn (N+2) ⟨0, hL, columnTop_reaches_initial N hN b hclear⟩
  exact ⟨k, hk, he.symm⟩

/-- Claim 4.4's lower count, with the first-contact geometry made explicit. -/
theorem frozenSquares_return_lower {N L j : Nat} (hN : 0 < N)
    {b : List (Option Point)} (hclear : some origin ∉ b) (hL : 0 < L)
    (hreturn : staticWall (frozenSquares N b : Set Point) initialWall L = initialWall)
    (x : Int) (hx : 1 ≤ x)
    (heast : wallStart (staticWall (frozenSquares N b : Set Point) initialWall (j+1)) = (x+1,0))
    (hprefix : ∀ i, i ≤ j →
      (wallStart (staticWall (frozenSquares N b : Set Point) initialWall i)).2 < (N : Int)) :
    j + 2*N + 5 ≤ L := by
  let B : Set Point := frozenSquares N b
  obtain ⟨k, hk, htop⟩ := columnTop_in_initial_cycle hN hclear hL hreturn
  have htopstart : wallStart (staticWall B initialWall k) = (0, (N : Int)) := by
    rw [htop]
    simp [wallStart, columnTop]
  have hjk : j < k := by
    by_contra h
    have hp := hprefix k (by omega)
    rw [htop] at hp
    simp [wallStart, columnTop] at hp
  have htopnext : wallStart (staticWall B initialWall (k+1)) = (-1, (N : Int)) := by
    change wallStart (nextWall B (staticWall B initialWall k)) = _
    rw [nextWall_start, htop]
    simp [wallEnd, wallStart, columnTop, tangentSide, sideNeighbor]
  have hfinish : wallStart (staticWall B initialWall L) = (0,0) := by
    rw [hreturn]
    rfl
  have hn := staticWall_potential_bound B initialWall (fun v => v.2-v.1)
    wall_northwest_potential (show j+1 ≤ k by omega)
  have hs := staticWall_potential_bound B initialWall (fun v => v.1-v.2)
    wall_southeast_potential (show k+1 ≤ L by omega)
  rw [htopstart, heast] at hn
  rw [hfinish, htopnext] at hs
  dsimp only at hn hs
  omega

end AngelDevil
