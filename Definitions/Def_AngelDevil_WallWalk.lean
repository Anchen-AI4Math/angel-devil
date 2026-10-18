import Definitions.Def_AngelDevil_SquareBoundary

namespace AngelDevil

abbrev Wall := Point × SquareSide

/-- Counterclockwise rotation of the outward normal: occupied squares are left. -/
def tangentSide (d : SquareSide) : SquareSide :=
  (!d.1, if d.1 then !d.2 else d.2)

def wallOutside (w : Wall) : Point := sideNeighbor w.1 w.2

def IsBoundaryWall (B : Set Point) (w : Wall) : Prop :=
  w.1 ∈ B ∧ wallOutside w ∉ B

/-- The corner rule for shrunken blocks. An empty side-neighbor takes
priority over a diagonally touching block, so the walker passes through the gap. -/
noncomputable def nextWall (B : Set Point) (w : Wall) : Wall := by
  classical
  let t := tangentSide w.2
  let a := sideNeighbor w.1 t
  let b := sideNeighbor a w.2
  exact if a ∉ B then (w.1, t)
    else if b ∉ B then (a, w.2)
    else (b, oppositeSide t)

noncomputable def previousWall (B : Set Point) (w : Wall) : Wall := by
  classical
  let t := oppositeSide (tangentSide w.2)
  let a := sideNeighbor w.1 t
  let b := sideNeighbor a w.2
  exact if a ∉ B then (w.1, t)
    else if b ∉ B then (a, w.2)
    else (b, oppositeSide t)

def initialWall : Wall := ((-1, 0), (false, false))

def wallObstacles (burned : List (Option Point)) : Set Point :=
  {v | v.1 < 0 ∨ some v ∈ burned}

/-- Two wall transitions per turn fit inside the power-two movement box. -/
noncomputable def wallHistory (burned : List (Option Point)) : Wall :=
  if _h : burned = [] then initialWall else
  let w := wallHistory burned.dropLast
  nextWall (wallObstacles burned) (nextWall (wallObstacles burned) w)
termination_by burned.length
decreasing_by
  have hp := List.length_pos_iff.mpr _h
  simp only [List.length_dropLast]
  omega

noncomputable def wallAngel : AngelStrategy :=
  fun _ burned => wallOutside (wallHistory burned)

def traceObstacles (D : DevilStrategy) (i : Nat) : Set Point :=
  wallObstacles (play wallAngel D (i / 2 + 1)).burned

noncomputable def wallTrace (D : DevilStrategy) : Nat → Wall
  | 0 => initialWall
  | i+1 => nextWall (traceObstacles D i) (wallTrace D i)

end AngelDevil
