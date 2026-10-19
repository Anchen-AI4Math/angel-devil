"""Generate a Lean proof tree; Python search is not trusted by the proof kernel."""
from functools import lru_cache
from pathlib import Path

@lru_cache(None)
def solve(n, x, blocked):
    blocked = frozenset(blocked)
    for z in sorted(range(x-5,x+6), key=lambda z: abs(z-x)):
        new = blocked | {z}
        if n == 1:
            if {x-1,x,x+1} <= new:
                return z
        elif all(solve(n-1,x+d,tuple(sorted(new))) is not None for d in [-1,0,1]):
            return z
    return None

def proof(n,x,blocked,indent):
    z=solve(n,x,tuple(sorted(blocked)))
    assert z is not None
    text=indent+f'refine ⟨⟨{z-x+5}, by decide⟩, ?_⟩\n'
    if n == 1:
        return text+indent+'intro j\n'+indent+'fin_cases j <;> decide\n'
    text+=indent+'intro j\n'+indent+'fin_cases j\n'
    for d in [-1,0,1]:
        sub=proof(n-1,x+d,blocked|{z},indent+'  ')
        text+=indent+'· '+sub[len(indent)+2:]
    return text

root=Path(__file__).resolve().parents[1]
text=('import Solutions.KingGuard\n\nnamespace AngelDevil\n\n'
      'set_option maxRecDepth 2000\nset_option maxHeartbeats 2000000\n\n'
      '/-- Exhaustive five-burn line-guard certificate (three possible horizontal moves). -/\n'
      'theorem kingGuard_five_origin : KingGuard 4 0 ∅ := by\n  unfold KingGuard\n')
text+=proof(5,0,set(),'  ')+'\nend AngelDevil\n'
(root/'Solutions/KingGuardCertificate.lean').write_text(text,encoding='utf-8')
print('Generated a proof with explicit witnesses and kernel-checked finite cases.')
