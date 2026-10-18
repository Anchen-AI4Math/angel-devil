"""Package the geometric proof with an actual dependency on published Claim 4.2."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def body(name):
    s = (ROOT/'Solutions'/(name+'.lean')).read_text(encoding='utf-8')
    return s.split('namespace AngelDevil\n',1)[1].rsplit('end AngelDevil',1)[0]

s = ('import Definitions.Def_AngelDevil_WallWalk\n'
     'import Theorems.Thm_AngelDevil_connectedSquares_perimeter\n\n'
     'namespace AngelDevil\n')
s += body('Foundation') + body('Histories').split('def stationary',1)[0]
s = s.replace('rw [(play_lengths A D n).1]; omega', 'rw [(play_lengths A D n).1]')
b = body('SquareBoundary')
s += b[b.index('theorem sideNeighbor_opposite '):b.index('theorem sideNeighbor_ne ')]
s += b[b.index('theorem mem_boundaryWalls '):]
for name in ['WallWalk','WallStrategy','WallGeometry','WallComponent','WallTruncation','WallNoReturn']:
    s += body(name)
s += '''
end AngelDevil

theorem solution (D : AngelDevil.DevilStrategy) (hnice : AngelDevil.Nice 2 D)
    (n : Nat) (hn : 0 < n) : AngelDevil.wallTrace D n ≠ AngelDevil.initialWall :=
  AngelDevil.wallTrace_never_returns D hnice n hn
'''
assert 'sorry' not in s
(ROOT/'platform/no-return-solution.lean').write_text(s,encoding='utf-8')
