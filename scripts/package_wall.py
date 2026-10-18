"""Package the closed no-return-to-win implication, with no target imports."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def body(name):
    s = (ROOT/'Solutions'/(name+'.lean')).read_text(encoding='utf-8')
    return s.split('namespace AngelDevil\n',1)[1].rsplit('end AngelDevil',1)[0]

s = 'import Definitions.Def_AngelDevil_WallWalk\n\nnamespace AngelDevil\n'
s += body('Foundation')
s += body('Histories').split('def stationary',1)[0]
# Mathlib's simp/rw extensions close this reflexive bound immediately.
s = s.replace('rw [(play_lengths A D n).1]; omega', 'rw [(play_lengths A D n).1]')
b = body('SquareBoundary')
s += b[b.index('theorem sideNeighbor_opposite '):b.index('theorem sideNeighbor_ne ')]
s += body('WallWalk') + body('WallStrategy')
s += '''
end AngelDevil

theorem solution
    (hreturn : ∀ D, AngelDevil.Nice 2 D → ∀ n, 0 < n →
      AngelDevil.wallTrace D n ≠ AngelDevil.initialWall) :
    AngelDevil.NiceAngelWins 2 :=
  AngelDevil.niceAngelWins_of_wall_no_return hreturn
'''
assert 'sorry' not in s
(ROOT/'platform/wall-conditional-solution.lean').write_text(s,encoding='utf-8')
