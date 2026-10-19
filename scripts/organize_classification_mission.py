"""Curate the existing public mission; reuse immutable, already proved nodes."""
import json
from pathlib import Path
from prepare_proposal import authenticate, call

ROOT = Path(__file__).resolve().parents[1]
MID = '6ca204ff-f20b-44be-9d36-410667a76662'
GOAL = '78319c36-be90-44b7-ae39-6f212616b326'
NAME = 'Angel-Devil: Complete Integer-Power Classification'
OUT = ROOT / 'verification/classification-mission'

def save(name, data):
    OUT.mkdir(exist_ok=True)
    (OUT / (name + '.json')).write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

def find_mission(token):
    offset = 0
    while True:
        r = call(f'/missions?limit=100&offset={offset}', token=token)
        rows = r['missions']
        for m in rows:
            if m['id'] == MID:
                return m
        if len(rows) < 100:
            raise RuntimeError('Existing mission not found')
        offset += 100

def main():
    token = authenticate()
    before = find_mission(token)
    save('before', before)
    assert before['visibility'] == 'public'
    goal = call('/theorems/' + GOAL, token=token)
    save('goal', goal)
    payload = {'name': NAME, 'main_statement': GOAL,
               'description': (ROOT/'platform/classification/mission-description.md').read_text(encoding='utf-8')}
    save('metadata-request', payload)
    save('metadata-response', call('/missions/' + MID, payload, method='PATCH', token=token))
    path = '/missions/' + MID + '/milestones'
    existing = call(path + '?limit=100&offset=0', token=token)
    save('milestones-before', existing)
    additions = [
        {'title': 'Section 1.1 (Kutz): the Devil defeats the king',
         'milestone_description': 'Kutz (2004), Chapter 1, Section 1.1, pp. 2–3, describes Berlekamp\'s king-capture result. In the shared infinite-board game, there exists one ordinary Devil strategy D such that every power-one Angel strategy A fails to survive. The formal statement is existential in D before universal in A. No optimal capture time or illustrated board-size bound is asserted.',
         'theorem_id': '26888492-cdea-4b37-b3a2-327d25204e18', 'sort_order': 0},
        {'title': 'Theorem 4.6 (Mathe): the Angel of power two wins',
         'milestone_description': 'Mathe (2007), Theorem 4.6: the Angel of power 2 wins. There exists a single power-two Angel strategy surviving forever against every ordinary Devil strategy on the infinite integer lattice, with the shared Devil-first and passing conventions. This is the original mission goal, retained as a source milestone under the complete classification.',
         'theorem_id': '6204cf5d-3e21-4e77-91ee-856e578b4253', 'sort_order': 3}]
    for spec in additions:
        found = next((m for m in existing['milestones'] if (m.get('theorem') or {}).get('id') == spec['theorem_id']), None)
        if found:
            continue
        save('create-' + str(spec['sort_order']) + '-request', spec)
        save('create-' + str(spec['sort_order']) + '-response', call(path, spec, token=token))
    for m in existing['milestones']:
        tid = (m.get('theorem') or {}).get('id')
        order = {'76719177-828c-4447-b573-06ec5a9f0684': 1,
                 '880e0f8b-5ca9-4de7-965e-33979f37fbaf': 2}.get(tid)
        if order is not None and order != m['sort_order']:
            call('/milestones/' + m['id'], {'sort_order': order}, method='PATCH', token=token)
    after = find_mission(token)
    milestones = call(path + '?limit=100&offset=0', token=token)
    save('after', after)
    save('milestones-after', milestones)
    assert after['name'] == NAME and after['main_theorem']['theorem_id'] == GOAL
    assert after['main_theorem']['status'] == 'Proved'
    assert len(milestones['milestones']) == 4
    assert all(m['completed'] and m['theorem']['status'] == 'Proved' for m in milestones['milestones'])
    print(NAME, 'public; goal Proved; 4/4 source milestones completed')

if __name__ == '__main__':
    main()
