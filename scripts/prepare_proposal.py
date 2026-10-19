"""Create/update an editable proposal only. Human confirmation/launch is separate.

Set PROVE2ME_CREDENTIALS to a saved credentials JSON file, or PROVE2ME_API_KEY.
No credential is printed or saved in this repository.
"""
from pathlib import Path
import os, json, urllib.request, urllib.parse, sys
sys.stdout.reconfigure(encoding='utf-8')
ROOT = Path(__file__).resolve().parents[1]
BASE = 'https://prove2.me/api/v1'

def call(path, data=None, method=None, token=None):
    headers = {'Content-Type': 'application/json'}
    if token: headers['Authorization'] = 'Bearer ' + token
    req = urllib.request.Request(BASE + path, headers=headers, method=method,
        data=json.dumps(data).encode() if data is not None else None)
    with urllib.request.urlopen(req, timeout=60) as response:
        return json.load(response)

def authenticate():
    key = os.environ.get('PROVE2ME_API_KEY')
    if not key:
        key = json.loads(Path(os.environ['PROVE2ME_CREDENTIALS']).read_text(
            encoding='utf-8-sig'))['api_key']
    auth = call('/agent/refresh', {'api_key': key})
    if auth.get('version') != '0.13.0':
        raise RuntimeError('Review current API documentation before using this script')
    return auth['access_token']

def main():
    token = authenticate()
    readbacks = json.loads((ROOT/'verification/readbacks.json').read_text(encoding='utf-8'))
    fields = call('/fields?q=combinatorics', token=token)['fields']
    field = next(f['id'] for f in fields if f['slug'] == 'combinatorics')
    meta = {'name': 'The Angel of Power 2 Wins (Mathe)',
            'description': (ROOT/'platform/proposal-description.md').read_text(encoding='utf-8'),
            'mission_type': 'ResearchPaper', 'field_ids': [field],
            'env': '0df444a360eaa60ab8c11dca51a86af692955474', 'visibility': 'public'}
    path = ROOT/'platform/proposal-state.json'
    if path.exists():
        pid = json.loads(path.read_text())['id']
        proposal = call('/mission-proposals/'+pid, token=token)
        if proposal['status'] != 'Draft': raise RuntimeError('Proposal is no longer Draft')
    else:
        proposal = call('/mission-proposals', meta, token=token)
        pid = proposal['id']
        path.write_text(json.dumps({'id':pid,'status':proposal['status']},indent=2))
    source = ('Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; '
              'https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination.')
    items = [{'kind':'definition','definition_name':'AngelDevil_Game',
              'definition_title':'Angel and Devil: infinite-board game and strategies',
              'definition':(ROOT/'Definitions/Def_AngelDevil_Game.lean').read_text(encoding='utf-8'),
              'natural_language_statement':'Integer lattice game with Devil-first rounds, passing, history-dependent strategies, legal survival, Nice Devil restrictions, unbounded escape, and confinement of every finite safe prefix. Conventions follow Sections 1-2, Definitions 2.2, 2.3, 2.5 and equation (2).',
              'source':source+' Sections 1-2, manuscript pp. 1-3.', 'readback':readbacks['definitions']}]
    specs = [
      ('nice_devil_reduction','Theorem 2.7: reduction to a Nice Devil',
       '(p : Nat) (hp : 0 < p) : ¬ AngelDevil.AngelWins p → ∃ N, 0 < N ∧ AngelDevil.NiceCanConfine p N',
       'For every positive integer power, if the Angel has no winning strategy, some Nice Devil can keep every finite safe play in a fixed box of positive integer radius. This formulation includes the determinacy observation from the introduction in addition to Theorem 2.7.',
       'Theorem 2.7, manuscript p. 3, with the introductory determinacy observation on p. 1.', 'reduction'),
      ('power_two_beats_nice_devil','Theorem 4.5: power two escapes every Nice Devil',
       ': AngelDevil.NiceAngelWins 2',
       'There exists one power-two Angel strategy that survives against every Nice Devil and, against each such opponent, reaches outside every finite box centred at the origin.',
       'Theorem 4.5, manuscript p. 8.', 'nice_win'),
      ('power_two_wins','Theorem 4.6: the Angel of power two wins',
       ': AngelDevil.AngelWins 2',
       'There exists a single power-two Angel strategy that makes legal uneaten landings forever against every Devil strategy on the infinite integer lattice, with the Devil moving first and permitted to pass.',
       'Theorem 4.6, manuscript p. 8.', 'main_goal')]
    for name,title,statement,prose,ref,key in specs:
        items.append({'kind':'theorem','theorem_name':'AngelDevil.'+name,
            'theorem_title':title,'formal_statement':'theorem AngelDevil.'+name+' '+statement+' := by sorry',
            'preamble':'import Definitions.Def_AngelDevil_Game',
            'natural_language_statement':prose,'source':source+' '+ref,'readback':readbacks[key]})
    ids=[]
    for item in items:
        item.update({'tags':['combinatorics','game-theory','angel-problem'],'readback_model':'gpt-6'})
        query = item.get('theorem_name',item.get('definition_name'))
        existing=call('/theorems?'+urllib.parse.urlencode({'q':'"'+query+'"','limit':100}),token=token)
        exact=[x for x in existing.get('theorems',[]) if x.get('theorem_name')==query]
        if exact: raise RuntimeError('Existing platform declaration found: '+query+'; review reuse first')
        result=call('/mission-proposals/'+pid+'/items',item,token=token)
        ids.append(result['id'])
        print('Prepared',query)
    call('/mission-proposals/'+pid,{'main_item_id':ids[-1],'item_order':ids},method='PATCH',token=token)
    for idx in [1,2]:
        item=items[idx]
        call('/mission-proposals/'+pid+'/milestones',{
            'item_id':ids[idx], 'milestone_title':item['theorem_title'],
            'milestone_description':item['natural_language_statement']},token=token)
    final=call('/mission-proposals/'+pid,token=token)
    (ROOT/'platform/proposal-readback.json').write_text(json.dumps(final,ensure_ascii=False,indent=2),encoding='utf-8')
    path.write_text(json.dumps({'id':pid,'status':final['status'],
        'item_ids':ids,'main_item_id':ids[-1],'api_version':'0.12.7'},indent=2))
    print('Proposal',pid,'status',final['status'],'items',len(final['items']))

if __name__=='__main__': main()
