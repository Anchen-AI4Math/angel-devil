"""Package closed local proofs using real published theorem dependencies."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def body(module):
    text = (ROOT / 'Solutions' / (module + '.lean')).read_text(encoding='utf-8')
    return text.split('namespace AngelDevil\n', 1)[1].rsplit('end AngelDevil', 1)[0]

def declaration(text, name):
    start = text.index('theorem ' + name + ' ')
    match = re.search(r'\n(?:theorem|def) ', text[start + 1:])
    end = start + 1 + match.start() if match else len(text)
    # Trailing comments belong to the next declaration, and are harmless.
    return text[start:end] + '\n'

reduced = body('ReducedJourney')
nice = body('NiceReduction')
conf = body('Confinement')
without_journey = reduced.replace(declaration(reduced, 'reducedJourney_is_journey'), '')
claim_body = without_journey + nice[:nice.index('theorem visited_take ')]
claim_body += nice[nice.index('theorem endpoint_eligible_at_earlier_prefix '):]
conf_body = body('Foundation') + body('Histories')
conf_body += declaration(reduced, 'reducedJourney_endpoint')
conf_body += declaration(reduced, 'take_last')
for name in ['niceReduction_eq_some_iff', 'niceReduction_is_nice', 'visited_take',
             'past_devil_move_mem', 'safe_prefix_allowed']:
    conf_body += declaration(nice, name)
conf_body += conf

specs = json.loads((ROOT / 'platform/section2-statements.json').read_text(encoding='utf-8'))
for key, source, imports, target in [
    ('claim-2-6', claim_body,
     'import Theorems.Thm_AngelDevil_reducedJourney_is_journey\n', 'reducedJourney_allowed'),
    ('theorem-2-4', conf_body,
     'import Theorems.Thm_AngelDevil_reducedJourney_allowed\n', 'confinement_to_nice')]:
    header = 'import Definitions.Def_AngelDevil_NiceReduction\n' + imports
    statement = specs[key]['formal_statement'].replace('theorem AngelDevil.' + target,
                                                      'theorem solution', 1)
    statement = statement.removesuffix(' := by sorry')
    args = 'p D h ha' if key == 'claim-2-6' else 'p N D hc'
    result = header + '\nnamespace AngelDevil\n' + source + '\nend AngelDevil\n'
    result += '\nopen AngelDevil\n' + statement + ' := by\n  exact AngelDevil.' + target + ' ' + args + '\n'
    assert 'sorry' not in result
    (ROOT / 'platform' / (key + '-solution.lean')).write_text(result, encoding='utf-8')
