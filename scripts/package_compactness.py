"""Build platform proof files with the intended compactness/determinacy edges."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def body(module):
    s = (ROOT/'Solutions'/(module+'.lean')).read_text(encoding='utf-8')
    return s.split('namespace AngelDevil\n',1)[1].rsplit('end AngelDevil',1)[0]

def decl(s, name):
    start = s.index('theorem '+name+' ')
    match = re.search(r'\n(?:theorem|def) ', s[start+1:])
    end = start+1+match.start() if match else len(s)
    return s[start:end]+'\n'

common = body('Foundation')
for name in ['current_zero', 'current_succ']:
    common += decl(body('Histories'), name)
common += body('FiniteHorizon')
compact = body('StrategyCompactness')
det = body('FiniteDeterminacy')
specs = json.loads((ROOT/'platform/compactness-statements.json').read_text(encoding='utf-8'))
uniform = decl(det,'uniform_confinement')
uniform_statement = uniform[:uniform.index(':= by')].strip().replace(
    'theorem uniform_confinement','theorem solution',1)
packages = [
    ('compactness', 'import Mathlib.Combinatorics.Compactness\n'
     'import Definitions.Def_AngelDevil_FiniteHorizon\n', common+compact,
     specs['compactness']['formal_statement'].replace(
         'theorem AngelDevil.finite_survival_compactness','theorem solution').removesuffix(' := by sorry'),
     'AngelDevil.finite_survival_compactness p hf'),
    ('finite-determinacy', 'import Mathlib.Combinatorics.Compactness\n'
     'import Definitions.Def_AngelDevil_FiniteGame\n',
     common+det[:det.index('theorem uniform_confinement ')],
     specs['finite-determinacy']['formal_statement'].replace(
         'theorem AngelDevil.finite_game_determined','theorem solution').removesuffix(' := by sorry'),
     'AngelDevil.finite_game_determined p T'),
    ('uniform-confinement',
     'import Theorems.Thm_AngelDevil_finite_survival_compactness\n'
     'import Theorems.Thm_AngelDevil_finite_game_determined\n'
     'import Mathlib.Combinatorics.Compactness\n',
     common+decl(compact,'no_win_has_finite_obstruction')+uniform,
     uniform_statement, 'AngelDevil.uniform_confinement p _hp h')]
for name, imports, source, statement, proof in packages:
    result = imports+'\nnamespace AngelDevil\n'+source+'\nend AngelDevil\n\n'
    result += 'open AngelDevil\n'+statement+' := by\n  exact '+proof+'\n'
    assert 'sorry' not in result
    (ROOT/'platform'/(name+'-solution.lean')).write_text(result,encoding='utf-8')
