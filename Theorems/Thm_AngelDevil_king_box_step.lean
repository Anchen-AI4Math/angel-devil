import Definitions.Def_AngelDevil_KingGuard
theorem AngelDevil.king_box_step (p : AngelDevil.Point) (B : Finset AngelDevil.Point) (h : AngelDevil.KingBoxReady p B) : ∃ z ∈ AngelDevil.kingBoard, ∀ q, AngelDevil.Jump 1 p q → q ∉ insert z B → AngelDevil.KingBoxReady q (insert z B) := by sorry
