import Solutions.WallGeometry

namespace AngelDevil

abbrev SquarePath (s : Finset Point) (u v : Point) : Prop :=
  Relation.ReflTransGen (fun a b => a ∈ s ∧ b ∈ s ∧ SquareAdjacent a b) u v

noncomputable def squareComponent (s : Finset Point) (root : Point) : Finset Point := by
  classical
  exact s.filter (SquarePath s root)

theorem squareAdjacent_symm {u v : Point} (h : SquareAdjacent u v) : SquareAdjacent v u := by
  obtain ⟨d, rfl⟩ := h
  exact ⟨oppositeSide d, sideNeighbor_opposite u d⟩

theorem squarePath_reverse {s : Finset Point} {u v : Point} (h : SquarePath s u v) :
    SquarePath s v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.head ⟨hstep.2.1, hstep.1, squareAdjacent_symm hstep.2.2⟩

theorem mem_squareComponent (s : Finset Point) (r v : Point) :
    v ∈ squareComponent s r ↔ v ∈ s ∧ SquarePath s r v := by
  classical
  simp [squareComponent]

theorem squareComponent_subset (s : Finset Point) (r : Point) : squareComponent s r ⊆ s := by
  intro v hv
  exact ((mem_squareComponent s r v).mp hv).1

theorem squareComponent_root {s : Finset Point} {r : Point} (hr : r ∈ s) :
    r ∈ squareComponent s r :=
  (mem_squareComponent s r r).mpr ⟨hr, Relation.ReflTransGen.refl⟩

theorem squareComponent_path {s : Finset Point} {r v : Point}
    (hp : SquarePath s r v) : SquarePath (squareComponent s r) r v := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v hpath hstep ih =>
    have hu := (mem_squareComponent s r u).mpr ⟨hstep.1, hpath⟩
    have hv := (mem_squareComponent s r v).mpr ⟨hstep.2.1, hpath.tail hstep⟩
    exact ih.tail ⟨hu, hv, hstep.2.2⟩

theorem squareComponent_connected {s : Finset Point} {r : Point} (hr : r ∈ s) :
    SquaresConnected (squareComponent s r) := by
  refine ⟨⟨r, squareComponent_root hr⟩, ?_⟩
  intro u hu v hv
  have hp := squareComponent_path ((mem_squareComponent s r u).mp hu).2
  have hq := squareComponent_path ((mem_squareComponent s r v).mp hv).2
  exact (squarePath_reverse hp).trans hq

theorem squareComponent_adjacent {s : Finset Point} {r u v : Point}
    (hu : u ∈ squareComponent s r) (hv : v ∈ s) (h : SquareAdjacent u v) :
    v ∈ squareComponent s r := by
  obtain ⟨hus, hp⟩ := (mem_squareComponent s r u).mp hu
  exact (mem_squareComponent s r v).mpr ⟨hv, hp.tail ⟨hus, hv, h⟩⟩

theorem nextWall_component {s : Finset Point} {r : Point} {w : Wall}
    (hw : w.1 ∈ squareComponent s r) :
    nextWall (squareComponent s r : Set Point) w = nextWall (s : Set Point) w := by
  classical
  unfold nextWall
  dsimp only
  by_cases ha : sideNeighbor w.1 (tangentSide w.2) ∈ s
  · have haC := squareComponent_adjacent hw ha ⟨tangentSide w.2, rfl⟩
    by_cases hb : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∈ s
    · have hbC := squareComponent_adjacent haC hb ⟨w.2, rfl⟩
      simp [ha, haC, hb, hbC]
    · have hbC : sideNeighbor (sideNeighbor w.1 (tangentSide w.2)) w.2 ∉ squareComponent s r :=
        fun h => hb (squareComponent_subset s r h)
      simp [ha, haC, hb, hbC]
  · have haC : sideNeighbor w.1 (tangentSide w.2) ∉ squareComponent s r :=
      fun h => ha (squareComponent_subset s r h)
    simp [ha, haC]

theorem staticWall_component {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) (n : Nat) :
    staticWall (squareComponent s w.1 : Set Point) w n = staticWall (s : Set Point) w n := by
  have hc : IsBoundaryWall (squareComponent s w.1 : Set Point) w :=
    ⟨squareComponent_root hw.1, fun h => hw.2 (squareComponent_subset s w.1 h)⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change nextWall _ (staticWall _ w n) = nextWall _ (staticWall _ w n)
    rw [nextWall_component (staticWall_boundary hc n).1, ih]

/-- Even if the whole obstacle set is disconnected, this corner convention
keeps the walk on one side-connected component. -/
theorem finite_staticWall_cycle_bound {s : Finset Point} {w : Wall}
    (hw : IsBoundaryWall (s : Set Point) w) :
    ∃ L, 0 < L ∧ staticWall (s : Set Point) w L = w ∧ L ≤ 2*s.card+2 := by
  have hc : IsBoundaryWall (squareComponent s w.1 : Set Point) w :=
    ⟨squareComponent_root hw.1, fun h => hw.2 (squareComponent_subset s w.1 h)⟩
  obtain ⟨L, hL, heq, hb⟩ := connected_staticWall_cycle_bound
    (squareComponent_connected hw.1) hc
  rw [staticWall_component hw] at heq
  have hcard := Finset.card_le_card (squareComponent_subset s w.1)
  exact ⟨L, hL, heq, by omega⟩

end AngelDevil
