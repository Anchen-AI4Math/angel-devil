"""Publish audited Section 2 interfaces; receipts prevent automatic duplicates."""
from pathlib import Path
import argparse
import json
import urllib.parse
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE = ('Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; '
          'https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. ')
p = argparse.ArgumentParser()
p.add_argument('part', choices=['definition', 'theorems'])
a = p.parse_args()
receipt = ROOT / 'verification' / ('section2-' + a.part + '-job.json')
if receipt.exists():
    raise SystemExit('Receipt exists: poll its existing job handles')
readbacks = json.loads((ROOT/'verification/section2-readbacks.json').read_text(encoding='utf-8'))
assert all(readbacks.get(k) for k in ['definitions','claim-2-6','theorem-2-4','uniform-confinement'])
token = authenticate()

def check_new(name):
    r = call('/theorems?' + urllib.parse.urlencode({'q': '"'+name+'"', 'limit':100}), token=token)
    assert not any(t.get('theorem_name') == name for t in r.get('theorems', [])), name

if a.part == 'definition':
    name = 'AngelDevil_NiceReduction'
    check_new(name)
    payload = {
        'definition_name': name,
        'definition_title': 'Nice Devil transformation and allowed finite journeys',
        'definition': (ROOT/'Definitions/Def_AngelDevil_NiceReduction.lean').read_text(encoding='utf-8'),
        'natural_language_statement': (
            'For a finite history, a square is eligible for a Nice Devil precisely when it is not '
            'the origin and is outside the power-p neighbourhood of every position except the last. '
            'The transformed Devil applies the original Devil to the reduced history, and retains '
            'its selected square exactly when eligible; otherwise it passes. An allowed journey '
            'starts at the origin, has legal jumps, and never lands on any square selected by '
            'the Devil at an earlier prefix, including the selection immediately before landing.'),
        'source': SOURCE+'Definition 2.5 and following discussion, p. 2; equation (2), p. 3.',
        'tags':['combinatorics','game-theory','angel-problem'], 'env':ENV, 'private':False}
    result = call('/submit-definition', payload, token=token)
else:
    specs = json.loads((ROOT/'platform/section2-statements.json').read_text(encoding='utf-8'))
    descriptions = {
        'claim-2-6': ('Claim 2.6: allowed journeys remain allowed after reduction',
            'For every nonnegative integer power, every Devil strategy and every finite journey '
            'allowed against its Nice transformation, the reduced journey is allowed against the '
            'original Devil. Allowedness includes both bounded jumps and avoidance of all earlier '
            'Devil selections. The statement also covers power zero.', 'Claim 2.6, p. 3.'),
        'theorem-2-4': ('Theorem 2.4: transfer confinement to a Nice Devil',
            'Let p and N be nonnegative integers. If a Devil strategy keeps every safe finite '
            'play of the power-p Angel inside the box of radius N, then some Nice Devil does '
            'the same. The assumption ranges over every Angel strategy and every finite time, '
            'requiring safety only up to that time. This formalization includes the degenerate '
            'cases p = 0 and N = 0 in addition to the positive parameters in the paper.',
            'Theorem 2.4, pp. 2-3, with harmless zero-parameter extension.'),
        'uniform-confinement': ('Claim 2.1 and determinacy: a uniform confinement box',
            'For each positive integer power, if no single Angel strategy survives against '
            'every Devil, there is a positive integer radius and one Devil strategy such that '
            'every safe finite play remains inside that box. The radius and Devil are chosen '
            'before the Angel strategy and play length. This target includes the introductory '
            'determinacy observation as well as Claim 2.1; neither is assumed as an extra hypothesis.',
            'Claim 2.1, p. 2, and the introductory determinacy observation, p. 1.')}
    problems=[]
    for key, spec in specs.items():
        check_new(spec['theorem_name'])
        title, prose, ref = descriptions[key]
        problems.append({**spec, 'theorem_title':title, 'natural_language_statement':prose,
                         'source':SOURCE+ref, 'tags':['combinatorics','game-theory','angel-problem']})
    result = call('/submit-problem', {'problems':problems,'env':ENV,'private':False}, token=token)
receipt.write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result))
