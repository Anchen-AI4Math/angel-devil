import Definitions.Def_AngelDevil_Game
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod

namespace AngelDevil

/-- Four oriented sides of an integer unit square. -/
abbrev SquareSide := Bool × Bool

def sideNeighbor (v : Point) (d : SquareSide) : Point :=
  if d.1 then (v.1, v.2 + if d.2 then -1 else 1)
  else (v.1 + if d.2 then -1 else 1, v.2)

def oppositeSide (d : SquareSide) : SquareSide := (d.1, !d.2)

def SquareAdjacent (u v : Point) : Prop := ∃ d, sideNeighbor u d = v

def exposedSides (s : Finset Point) (v : Point) : Finset SquareSide :=
  Finset.univ.filter (fun d => sideNeighbor v d ∉ s)

/-- Number of unit boundary sides, including sides surrounding holes. -/
def squarePerimeter (s : Finset Point) : Nat :=
  ∑ v ∈ s, (exposedSides s v).card

def SquaresConnected (s : Finset Point) : Prop :=
  s.Nonempty ∧ ∀ a ∈ s, ∀ b ∈ s,
    Relation.ReflTransGen (fun u v => u ∈ s ∧ v ∈ s ∧ SquareAdjacent u v) a b

/-- A wall records its occupied square and the direction of its empty neighbor. -/
def boundaryWalls (s : Finset Point) : Finset (Point × SquareSide) :=
  s.biUnion (fun v => (exposedSides s v).image (fun d => (v, d)))

end AngelDevil
