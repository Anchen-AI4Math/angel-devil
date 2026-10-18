"""Publish Claim 4.2 interfaces; mutations have persistent receipt guards."""
from pathlib import Path
import argparse
import json
import urllib.parse
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser()
p.add_argument('part', choices=['definition', 'theorem'])
a = p.parse_args()
receipt = ROOT/'verification'/('boundary-'+a.part+'-job.json')
if receipt.exists():
    raise SystemExit('Receipt exists: poll the recorded job instead')
assert (ROOT/'verification/boundary-readback.md').exists()
token = authenticate()
name = ('AngelDevil_SquareBoundary' if a.part == 'definition'
        else 'AngelDevil.connectedSquares_perimeter')
existing = call('/theorems?'+urllib.parse.urlencode({'q':'"'+name+'"','limit':100}), token=token)
assert not any(x.get('theorem_name') == name for x in existing.get('theorems', []))
common = {'env':'0df444a360eaa60ab8c11dca51a86af692955474', 'private':False,
          'source': 'Mathe, The Angel of power 2 wins (2007), '
          'https://doi.org/10.1017/S0963548306008303, author manuscript p. 6, '
          'Definition 4.1 and Claim 4.2.',
          'tags':['combinatorics','game-theory','angel-problem']}
if a.part == 'definition':
    payload = {**common, 'definition_name':name,
       'definition_title':'Side-connected integer squares and their unit boundary',
       'definition':(ROOT/'Definitions/Def_AngelDevil_SquareBoundary.lean').read_text(encoding='utf-8'),
       'natural_language_statement':
       'Squares are indexed by integer pairs. The four side neighbors differ by '
       'one in exactly one coordinate. A finite set is connected when it is nonempty '
       'and any two members can be joined by a finite sequence of side-neighbor steps '
       'within the set. Each exposed side is a direction from an occupied square to '
       'an unoccupied neighbor. The perimeter counts all such sides, including hole '
       'boundaries. The wall set records the occupied square and side direction.'}
    result = call('/submit-definition', payload, token=token)
else:
    payload = {**common, 'theorem_name':name,
       'theorem_title':'Claim 4.2: boundary bound for connected squares',
       'formal_statement':'theorem AngelDevil.connectedSquares_perimeter '
       '{s : Finset AngelDevil.Point} (h : AngelDevil.SquaresConnected s) : '
       'AngelDevil.squarePerimeter s ≤ 2 * s.card + 2 := by sorry',
       'preamble':'import Definitions.Def_AngelDevil_SquareBoundary',
       'natural_language_statement':
       'Let $S$ be a finite nonempty set of integer unit squares, connected by shared '
       'sides, and let $P(S)$ count all unit boundary sides, including boundaries '
       'of holes. Then\n\n$$P(S) \\le 2|S|+2.$$\n\n'
       'This is the connected-square perimeter estimate used in the wall-counting '
       'argument for the Angel strategy.'}
    result = call('/submit-problem', payload, token=token)
receipt.write_text(json.dumps(result, indent=2), encoding='utf-8')
print(json.dumps(result))
