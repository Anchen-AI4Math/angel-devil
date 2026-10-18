"""Publish the audited finite-horizon interfaces without retrying mutations."""
from pathlib import Path
import argparse
import json
import urllib.parse
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
ENV = '0df444a360eaa60ab8c11dca51a86af692955474'
SOURCE = ('Mathe, The Angel of power 2 wins (2007), '
          'https://doi.org/10.1017/S0963548306008303, author manuscript ')
p=argparse.ArgumentParser()
p.add_argument('part',choices=['horizon','game','theorems'])
a=p.parse_args()
receipt=ROOT/'verification'/('compactness-'+a.part+'-job.json')
if receipt.exists(): raise SystemExit('Poll existing job receipt instead')
audit=json.loads((ROOT/'verification/compactness-readbacks.json').read_text(encoding='utf-8'))
assert all(audit.get(k) for k in ['horizon-definitions','game-definitions','compactness','finite-determinacy'])
t=authenticate()

def check_new(name):
    r=call('/theorems?'+urllib.parse.urlencode({'q':'"'+name+'"','limit':100}),token=t)
    assert not any(x.get('theorem_name')==name for x in r.get('theorems',[])), name

if a.part!='theorems':
    suffix='FiniteHorizon' if a.part=='horizon' else 'FiniteGame'
    name='AngelDevil_'+suffix
    check_new(name)
    prose=(
      'Safety for n rounds requires every one of the first n jumps to be legal and to avoid all '
      'squares selected so far. Finite-horizon winning means one Angel strategy is safe for that '
      'horizon against every Devil. Strategy inputs are visited and burned histories. Legal '
      'displacements are encoded by pairs of integers from 0 through 2p, translated by minus p '
      'in each coordinate. The encoding retains legal choices and replaces illegal choices by staying put.'
      if a.part=='horizon' else
      'Finite viability is defined recursively: zero further rounds are always viable; one more '
      'round is viable when every optional Devil selection admits a safe Angel landing with a '
      'viable remaining state. The finite Angel selects such a landing when one exists. A bad '
      'Devil move makes every safe landing nonviable when such a move exists. Burn-history '
      'reconstruction turns these state-based choices into a total history-only Devil strategy. '
      'Off-path choices and exhausted horizons have explicitly defined defaults.')
    r=call('/submit-definition',{'definition_name':name,
       'definition_title':'Finite-horizon safety and bounded Angel moves' if a.part=='horizon' else 'Finite-game viability and history-based counterstrategies',
       'definition':(ROOT/'Definitions'/('Def_'+name+'.lean')).read_text(encoding='utf-8'),
       'natural_language_statement':prose,'source':SOURCE+'pp. 1-2: determinacy observation and Claim 2.1; auxiliary formalization definitions.',
       'env':ENV,'private':False,'tags':['combinatorics','game-theory','angel-problem']},token=t)
else:
    specs=json.loads((ROOT/'platform/compactness-statements.json').read_text(encoding='utf-8'))
    prose={
      'compactness':('Finite-horizon survival yields an infinite winning strategy',
        'For any nonnegative integer power, suppose that for every finite number n of rounds '
        'there exists an Angel strategy that remains safe for n rounds against every Devil. '
        'Then a single Angel strategy remains safe forever against every Devil. The finite '
        'strategies may depend on n; the conclusion uses one strategy for all rounds.',
        'p. 2, Claim 2.1 proof: the suitable limit of finite-horizon strategies.'),
      'finite-determinacy':('Finite-horizon Angel-Devil determinacy',
        'For every nonnegative power p and finite horizon T, either one Angel strategy is safe '
        'for T rounds against every Devil, or one Devil strategy prevents every Angel strategy '
        'from being safe for T rounds. Both strategies use the original history interfaces. '
        'At horizon zero the first alternative holds. This is the finite-horizon determinacy '
        'step used with compactness in the confinement argument.',
        'pp. 1-2, determinacy observation and Claim 2.1 proof; finite-horizon intermediate statement.')}
    problems=[]
    for key,spec in specs.items():
        check_new(spec['theorem_name'])
        title,description,ref=prose[key]
        problems.append({**spec,'theorem_title':title,'natural_language_statement':description,
                         'source':SOURCE+ref,'tags':['combinatorics','game-theory','angel-problem']})
    r=call('/submit-problem',{'problems':problems,'env':ENV,'private':False},token=t)
receipt.write_text(json.dumps(r,indent=2),encoding='utf-8')
print(json.dumps(r))
