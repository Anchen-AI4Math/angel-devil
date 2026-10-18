"""Publish wall-walk definitions and the geometric no-return interface."""
from pathlib import Path
import argparse
import json
import urllib.parse
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('part',choices=['definition','theorems'])
a = p.parse_args()
receipt = ROOT/'verification'/('wall-'+a.part+'-job.json')
if receipt.exists(): raise SystemExit('Poll recorded jobs; do not resubmit')
assert (ROOT/'verification/wall-readback.md').exists()
token = authenticate()
common = {'env':'0df444a360eaa60ab8c11dca51a86af692955474','private':False}
source = ('Mathe, The Angel of power 2 wins (2007), '
          'https://doi.org/10.1017/S0963548306008303; author manuscript '
          'pp. 6-8, octagonal wall-following rule, Claim 3.1 analogue, '
          'Proposition 4.3 and Theorem 4.5. Two wall transitions per turn '
          'give an admissible power-two implementation; no-return is the remaining geometric obligation.')

def check_new(name):
    r=call('/theorems?'+urllib.parse.urlencode({'q':'"'+name+'"','limit':100}),token=token)
    assert not any(x.get('theorem_name')==name for x in r.get('theorems',[]))

if a.part == 'definition':
    check_new('AngelDevil_WallWalk')
    result=call('/submit-definition', {**common,
      'definition_name':'AngelDevil_WallWalk',
      'definition_title':'Octagonal boundary walk and the power-two wall strategy',
      'definition':(ROOT/'Definitions/Def_AngelDevil_WallWalk.lean').read_text(encoding='utf-8'),
      'natural_language_statement':
      'A directed wall is an occupied integer square with an outward side direction. '
      'The tangent points counterclockwise from the outward normal. To advance, first '
      'test the occupied square\'s tangent neighbor: if empty, turn around the same '
      'square, even when the diagonal square is occupied. Otherwise test the diagonal '
      'square: if empty, continue straight; if occupied, turn around the concave corner. '
      'Obstacles consist of all squares with negative first coordinate together with '
      'the recorded Devil choices. Starting with the east side of square (-1,0), '
      'the strategy performs exactly two wall transitions after each Devil move and '
      'lands in the outside square. Its state is reconstructed from the chronological '
      'burn history. The wall trace records individual transitions, using the same '
      'obstacle set for both transitions of a round.',
      'source':source,'tags':['angel-problem','combinatorics','game-theory']},token=token)
else:
    specs=[{
      'theorem_name':'AngelDevil.wallTrace_never_returns',
      'theorem_title':'Geometric no-return for the power-two wall trace',
      'formal_statement':'theorem AngelDevil.wallTrace_never_returns '
        '(D : AngelDevil.DevilStrategy) (hnice : AngelDevil.Nice 2 D) '
        '(n : Nat) (hn : 0 < n) : '
        'AngelDevil.wallTrace D n ≠ AngelDevil.initialWall := by sorry',
      'natural_language_statement':'Against every Nice Devil of power two, '
        'the specified boundary-walking strategy never encounters its initial '
        'directed wall at any positive wall-transition index. The initial wall is '
        'the east side of square (-1,0). The trace uses two wall transitions per '
        'Angel turn and the obstacle set after that turn\'s Devil move. This is '
        'the geometric no-return obligation underlying the escape argument; it '
        'does not assume non-repetition or escape.'}, {
      'theorem_name':'AngelDevil.niceAngelWins_of_wall_no_return',
      'theorem_title':'No-return of the wall trace implies the Nice Angel theorem',
      'formal_statement':'theorem AngelDevil.niceAngelWins_of_wall_no_return '
        '(hreturn : ∀ D, AngelDevil.Nice 2 D → ∀ n, 0 < n → '
        'AngelDevil.wallTrace D n ≠ AngelDevil.initialWall) : '
        'AngelDevil.NiceAngelWins 2 := by sorry',
      'natural_language_statement':'Assume that against every Nice Devil, '
        'the specified two-transition wall trace never returns to its initial '
        'directed wall at a positive index. Then there is one power-two Angel '
        'strategy that survives against every Nice Devil and, against each such '
        'Devil, leaves every finite box centered at the origin. The no-return '
        'premise is an explicit geometric assumption; this conditional theorem '
        'does not by itself establish that premise.'}]
    for spec in specs:
        check_new(spec['theorem_name'])
        spec.update({'preamble':'import Definitions.Def_AngelDevil_WallWalk',
          'source':source,'tags':['angel-problem','combinatorics','game-theory']})
    (ROOT/'platform/wall-statements.json').write_text(json.dumps(specs,indent=2),encoding='utf-8')
    result=call('/submit-problem',{**common,'problems':specs},token=token)
receipt.write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result))
