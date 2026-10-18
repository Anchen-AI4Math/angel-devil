import Solutions.WallNoReturn
import Solutions.FiniteDeterminacy

namespace AngelDevil

theorem power_two_beats_nice_devil : NiceAngelWins 2 :=
  niceAngelWins_of_wall_no_return wallTrace_never_returns

theorem power_two_wins : AngelWins 2 :=
  nice_escape_and_reduction_imply_win (nice_devil_reduction 2 (by omega))
    power_two_beats_nice_devil

end AngelDevil
