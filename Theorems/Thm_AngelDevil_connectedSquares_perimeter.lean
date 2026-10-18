import Definitions.Def_AngelDevil_SquareBoundary

/-- Platform reference statement, excluded from the closed local proof library. -/
theorem AngelDevil.connectedSquares_perimeter {s : Finset AngelDevil.Point}
    (h : AngelDevil.SquaresConnected s) : AngelDevil.squarePerimeter s ≤ 2 * s.card + 2 := by sorry
