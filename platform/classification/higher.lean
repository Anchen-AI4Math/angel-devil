import Definitions.Def_AngelDevil_KingGuard
import Definitions.Def_AngelDevil_FiniteGame
import Mathlib.Tactic.FinCases
import Theorems.Thm_AngelDevil_angelWins_mono
import Theorems.Thm_AngelDevil_power_two_wins

set_option maxRecDepth 2000
set_option maxHeartbeats 2000000

namespace AngelDevil



end AngelDevil

theorem solution (p : Nat) (hp : 2 ≤ p) : AngelDevil.AngelWins p :=
  AngelDevil.angelWins_mono hp AngelDevil.power_two_wins
