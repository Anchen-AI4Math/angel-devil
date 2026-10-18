import Definitions.Def_AngelDevil_WallWalk
import Solutions.SquareBoundary
import Solutions.Foundation

namespace AngelDevil

theorem tangentSide_twice (d : SquareSide) :
    tangentSide (tangentSide d) = oppositeSide d := by
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem tangentSide_opposite (d : SquareSide) :
    tangentSide (oppositeSide d) = oppositeSide (tangentSide d) := by
  rcases d with ⟨a,b⟩
  cases a <;> cases b <;> rfl

theorem oppositeSide_twice (d : SquareSide) : oppositeSide (oppositeSide d) = d := by
  rcases d with ⟨a,b⟩
  cases b <;> rfl

theorem sideNeighbor_commute (v : Point) (d e : SquareSide) :
    sideNeighbor (sideNeighbor v d) e = sideNeighbor (sideNeighbor v e) d := by
  rcases v with ⟨x,y⟩
  rcases d with ⟨a,b⟩
  rcases e with ⟨c,f⟩
  cases a <;> cases b <;> cases c <;> cases f <;>
    simp [sideNeighbor]

theorem nextWall_boundary {B : Set Point} {w : Wall} (h : IsBoundaryWall B w) :
    IsBoundaryWall B (nextWall B w) := by
  classical
  unfold nextWall
  dsimp only
  split
  · exact ⟨h.1, ‹_ ∉ B›⟩
  · split
    · exact ⟨by simpa using ‹¬ _ ∉ B›, ‹_ ∉ B›⟩
    · constructor
      · simpa using ‹¬ _ ∉ B›
      · unfold wallOutside
        dsimp only
        rw [sideNeighbor_commute (sideNeighbor w.1 _) w.2 _, sideNeighbor_opposite]
        exact h.2

theorem nextWall_jump {B : Set Point} (w : Wall) :
    Jump 1 (wallOutside w) (wallOutside (nextWall B w)) := by
  classical
  unfold nextWall
  dsimp only
  split
  · rcases w with ⟨⟨x,y⟩,a,b⟩
    cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, Jump]
  · split
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, Jump]
    · rcases w with ⟨⟨x,y⟩,a,b⟩
      cases a <;> cases b <;> simp [wallOutside, sideNeighbor, tangentSide, oppositeSide, Jump]

theorem previousWall_next_of_extension {B C : Set Point} (hBC : B ⊆ C)
    {w : Wall} (hw : IsBoundaryWall B w) (hout : wallOutside w ∉ C) :
    previousWall C (nextWall B w) = w := by
  classical
  rcases w with ⟨u,d⟩
  have hu : u ∈ C := hBC hw.1
  change sideNeighbor u d ∉ C at hout
  unfold nextWall
  dsimp only
  split
  · simp [previousWall, tangentSide_twice, oppositeSide_twice, hout]
  · rename_i ha
    have haC : sideNeighbor u (tangentSide d) ∈ C := hBC (by simpa using ha)
    split
    · simp [previousWall, sideNeighbor_opposite, hu, hout]
    · simp [previousWall, tangentSide_opposite, tangentSide_twice,
        oppositeSide_twice, sideNeighbor_opposite, haC, hu]

theorem nextWall_injective {B : Set Point} {v w : Wall}
    (hv : IsBoundaryWall B v) (hw : IsBoundaryWall B w)
    (heq : nextWall B v = nextWall B w) : v = w := by
  have h := congrArg (previousWall B) heq
  rw [previousWall_next_of_extension (fun _ h => h) hv hv.2,
    previousWall_next_of_extension (fun _ h => h) hw hw.2] at h
  exact h

/-- The old side-neighbor supplies the middle square in a concave turn. -/
theorem nextWall_support_path {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w) :
    Relation.ReflTransGen (fun u v => u ∈ B ∧ v ∈ B ∧ SquareAdjacent u v)
      w.1 (nextWall B w).1 := by
  classical
  unfold nextWall
  dsimp only
  split
  · exact Relation.ReflTransGen.refl
  · rename_i ha
    have haB : sideNeighbor w.1 (tangentSide w.2) ∈ B := by simpa using ha
    have first : Relation.ReflTransGen
        (fun u v => u ∈ B ∧ v ∈ B ∧ SquareAdjacent u v)
        w.1 (sideNeighbor w.1 (tangentSide w.2)) :=
      Relation.ReflTransGen.single ⟨hw.1, haB, tangentSide w.2, rfl⟩
    split
    · exact first
    · rename_i hb
      exact first.tail ⟨haB, by simpa using hb, w.2, rfl⟩

/-- A first repeated wall is the initial wall, even while the obstacle set grows.
The preservation of earlier empty squares is an explicit hypothesis here. -/
theorem first_wall_repeat_is_initial (B : Nat → Set Point) (w : Nat → Wall)
    (hmono : Monotone B) (hwall : ∀ n, IsBoundaryWall (B n) (w n))
    (hstep : ∀ n, w (n+1) = nextWall (B n) (w n))
    (hprotect : ∀ i j, i ≤ j → wallOutside (w i) ∉ B j)
    {i j : Nat} (hij : i < j) (heq : w i = w j)
    (hinj : ∀ a b, a < j → b < j → w a = w b → a = b) : i = 0 := by
  cases i with
  | zero => rfl
  | succ k =>
    have hj : j = (j-1)+1 := by omega
    have hk : k ≤ j-1 := by omega
    have hjstep : w j = nextWall (B (j-1)) (w (j-1)) := by
      calc
        w j = w ((j-1)+1) := congrArg w hj
        _ = _ := hstep (j-1)
    have hprev := congrArg (previousWall (B (j-1))) heq
    rw [hstep k, hjstep] at hprev
    rw [previousWall_next_of_extension (hmono hk) (hwall k) (hprotect k (j-1) hk),
      previousWall_next_of_extension (fun _ h => h) (hwall (j-1))
        (hprotect (j-1) (j-1) (Nat.le_refl _))] at hprev
    have he := hinj k (j-1) (by omega) (by omega) hprev
    omega

theorem two_wall_steps_legal {B : Set Point} {w : Wall} (hw : IsBoundaryWall B w) :
    IsBoundaryWall B (nextWall B (nextWall B w)) ∧
      Jump 2 (wallOutside w) (wallOutside (nextWall B (nextWall B w))) := by
  exact ⟨nextWall_boundary (nextWall_boundary hw),
    jump_add (nextWall_jump w) (nextWall_jump (nextWall B w))⟩

theorem wall_determined_by_outside_normal {v w : Wall}
    (hp : wallOutside v = wallOutside w) (hd : v.2 = w.2) : v = w := by
  apply Prod.ext _ hd
  calc
    v.1 = sideNeighbor (wallOutside v) (oppositeSide v.2) :=
      (sideNeighbor_opposite v.1 v.2).symm
    _ = sideNeighbor (wallOutside w) (oppositeSide w.2) := by rw [hp, hd]
    _ = w.1 := sideNeighbor_opposite w.1 w.2

end AngelDevil
