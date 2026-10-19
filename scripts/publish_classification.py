"""Idempotent, explicitly staged publication of the integer-power extension."""
from pathlib import Path
import json
import sys
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'platform/classification'
V = ROOT/'verification/classification-platform'
V.mkdir(exist_ok=True)
token = authenticate()
mode = sys.argv[1]
specs = json.loads((OUT/'problems.json').read_text(encoding='utf-8'))

def save(name, value):
    (V/name).write_text(json.dumps(value,indent=2),encoding='utf-8')

if mode == 'definition':
    p=V/'definition-receipt.json'
    if p.exists(): raise SystemExit('Receipt already exists; poll it')
    payload={'definition_name':'AngelDevil_KingGuard',
        'definition_title':'Finite line guards and a box invariant for king capture',
        'definition':(ROOT/'Definitions/Def_AngelDevil_KingGuard.lean').read_text(encoding='utf-8'),
        'natural_language_statement':
          'A finite line-guard strategy tree records five possible preparation burns and all king displacements. '
          'Four oriented copies guard a square box. The interface also specifies the corner preparation list, '
          'the finite board, and the burned-set projection. These are auxiliary definitions for formalizing '
          'the published chess-king capture argument, with radius 100 and 56 preparatory selections.',
        'source':specs[0]['source']+' The box constants implement the same argument with generous margins.',
        'env':'0df444a360eaa60ab8c11dca51a86af692955474',
        'tags':['combinatorics','game-theory','angel-problem']}
    r=call('/submit-definition',payload,token=token);save(p.name,r);print(r)
elif mode == 'problems':
    p=V/'problems-receipt.json'
    if p.exists():raise SystemExit('Receipt already exists; poll it')
    definition=json.loads((V/'definition-job.json').read_text())
    assert definition['status']=='PUBLISHED'
    payload={'problems':[{k:v for k,v in p.items() if k!='key'} for p in specs],
             'env':'0df444a360eaa60ab8c11dca51a86af692955474'}
    r=call('/submit-problem',payload,token=token);save(p.name,r);print(r)
elif mode == 'poll':
    for p in V.glob('*-receipt.json'):
        r=json.loads(p.read_text())
        jobs=([r] if 'job_id' in r else r.get('jobs',[]))
        for j in jobs:
            job=call('/publish-jobs/'+j['job_id'],token=token)
            name=('definition' if p.name.startswith('definition') else job['theorem_name'].split('.')[-1])
            save(name+'-job.json',job)
            print(name,job['status'],job.get('theorem_id'),job.get('error_message',''))
elif mode == 'proof-poll':
    for p in V.glob('*-submission.json'):
        receipt=json.loads(p.read_text())
        r=call('/verify?submission_id='+receipt['submission_id'],token=token)
        save(p.name.replace('-submission','-result'),r)
        print(p.stem,r['status'],r.get('error_message',''))
elif mode == 'graph':
    for p in specs:
        job=json.loads((V/(p['theorem_name'].split('.')[-1]+'-job.json')).read_text())
        tid=job['theorem_id']
        for suffix in ['', '/graph?depth=20','/decompositions','/open-leaves?limit=100&offset=0']:
            r=call('/theorems/'+tid+suffix,token=token)
            label=suffix.split('?')[0].strip('/') or 'state'
            save(p['key']+'-'+label+'.json',r)
        print(p['key'],tid,'graph saved')
else:
    raise SystemExit('Choose definition, problems, poll, proof-poll or graph')
