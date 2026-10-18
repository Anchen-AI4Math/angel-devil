import Definitions.Def_AngelDevil_NiceReduction
open AngelDevil
theorem AngelDevil.reducedJourney_allowed (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p (niceReduction p D) h) : Allowed p D (reducedJourney p h)  := by sorry
