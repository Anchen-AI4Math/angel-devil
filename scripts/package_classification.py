"""Reproduce the platform packages from the closed local proof modules."""
from pathlib import Path
import re
import json

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'platform/classification'
OUT.mkdir(exist_ok=True)

def theorem_blocks(module):
    s = (ROOT/'Solutions'/f'{module}.lean').read_text(encoding='utf-8')
    starts = list(re.finditer(r'^theorem (\w+)', s, re.M))
    result = {}
    for i, match in enumerate(starts):
        end = starts[i+1].start() if i+1 < len(starts) else s.rfind('end AngelDevil')
        chunk = s[match.start():end].strip()
        # A trailing documentation comment belongs to the next declaration.
        if '\n/-' in chunk:
            chunk = chunk[:chunk.rfind('\n/-')].rstrip()
        result[match[1]] = chunk
    return result

def select(module, names=None):
    blocks = theorem_blocks(module)
    return '\n\n'.join(blocks[n] for n in (names or blocks))

imports = ['Definitions.Def_AngelDevil_KingGuard', 'Definitions.Def_AngelDevil_FiniteGame',
           'Mathlib.Tactic.FinCases']

def package(key, body, tail, extra=()):
    text = '\n'.join('import '+i for i in imports + list(extra))
    text += '\n\nset_option maxRecDepth 2000\nset_option maxHeartbeats 2000000\n'
    text += '\nnamespace AngelDevil\n\n'+body+'\n\nend AngelDevil\n\n'+tail+'\n'
    assert 'sorry' not in text
    (OUT/f'{key}.lean').write_text(text, encoding='utf-8')

package('guard', select('KingGuardCertificate'),
    'theorem solution : AngelDevil.KingGuard 4 0 ∅ := AngelDevil.kingGuard_five_origin')
package('box', select('KingGuard')+'\n\n'+select('KingBox'),
    'theorem solution (p : AngelDevil.Point) (B : Finset AngelDevil.Point)\n'
    '    (h : AngelDevil.KingBoxReady p B) :\n'
    '    ∃ z ∈ AngelDevil.kingBoard, ∀ q, AngelDevil.Jump 1 p q →\n'
    '      q ∉ insert z B → AngelDevil.KingBoxReady q (insert z B) :=\n'
    '  AngelDevil.king_box_step p B h',
    ['Theorems.Thm_AngelDevil_kingGuard_five_origin'])

helpers = select('Foundation',['jump_self','jump_add','play_lengths'])+'\n\n'+select('Histories',['current_succ'])+'\n\n'
helpers += select('FiniteHorizon',['safeFor_mono'])+'\n\n'
helpers += select('FiniteDeterminacy',['badMove_spec','simulatedBurns_append',
    'simulatedBurns_play','historyDevil_at_play','not_viable_forces_failure'])+'\n\n'
helpers += select('KingGuard',['kingGuard_mono','kingGuard_translate'])+'\n\n'
helpers += select('KingBox',['kingBoard_mem','king_wall_coordinates','king_wall_inverse',
    'kingLineBurns_mem','kingLineBurns_mono','kingCorners_length','kingGuard_five',
    'kingLineReady_far','king_inside_board','kingBoxReady_mono'])+'\n\n'
helpers += select('KingCapture')
package('one', helpers,
    'theorem solution : ∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives 1 A D :=\n'
    '  AngelDevil.power_one_devil_wins',
    ['Theorems.Thm_AngelDevil_kingGuard_five_origin','Theorems.Thm_AngelDevil_king_box_step'])

package('mono', select('Foundation',['jump_mono'])+'\n\n'+
    select('PowerClassification',['survives_mono','angelWins_mono']),
    'theorem solution {p q : Nat} (hpq : p ≤ q) (h : AngelDevil.AngelWins p) :\n'
    '    AngelDevil.AngelWins q := AngelDevil.angelWins_mono hpq h')
package('higher','',
    'theorem solution (p : Nat) (hp : 2 ≤ p) : AngelDevil.AngelWins p :=\n'
    '  AngelDevil.angelWins_mono hp AngelDevil.power_two_wins',
    ['Theorems.Thm_AngelDevil_angelWins_mono','Theorems.Thm_AngelDevil_power_two_wins'])
package('classification', select('KingCapture',['power_one_not_wins']),
    'theorem solution (p : Nat) : AngelDevil.AngelWins p ↔ 2 ≤ p := by\n'
    '  constructor\n  · intro h\n    by_contra hp\n'
    '    exact AngelDevil.power_one_not_wins (AngelDevil.angelWins_mono (by omega) h)\n'
    '  · exact AngelDevil.power_ge_two_wins p',
    ['Theorems.Thm_AngelDevil_power_one_devil_wins','Theorems.Thm_AngelDevil_angelWins_mono',
     'Theorems.Thm_AngelDevil_power_ge_two_wins'])

KUTZ = ('Martin Kutz, The Angel Problem, Positional Games, and Digraph Roots (2004), '
        'Chapter 1, Section 1.1, pp. 2-3, Figures 1-3. '
        'https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf. ')
MATHE = ('Andras Mathe, The Angel of power 2 wins (2007), Theorem 4.6 and '
         'Section 1 game definition; https://doi.org/10.1017/S0963548306008303. ')
specs = [
 ('guard','kingGuard_five_origin','Five-burn preparation of a line guard',
  ': AngelDevil.KingGuard 4 0 ∅',
  'Starting with no blocked sites on a line, the Devil can prepare a blocked triple above a king in five burns, despite every intervening horizontal displacement being -1, 0, or 1.\n\nThe finite strategy predicate records four intervening moves and a final burn that completes the triple. This is the local preparation lemma used to guard a box boundary.',
  KUTZ+'Finite strategy certificate for Figure 2; index 4 represents five burns.'),
 ('box','king_box_step','Preservation of a guarded box against a chess king',
  '(p : AngelDevil.Point) (B : Finset AngelDevil.Point) (h : AngelDevil.KingBoxReady p B) : ∃ z ∈ AngelDevil.kingBoard, ∀ q, AngelDevil.Jump 1 p q → q ∉ insert z B → AngelDevil.KingBoxReady q (insert z B)',
  'Suppose the king is strictly inside the box [-100,100]^2, its corner boundary segments are blocked, and each side has a line guard whose preparation fits the remaining distance. Then there is a single square in the box for the Devil to block such that every subsequent legal king move preserves these conditions.\n\nThis formal invariant implements the four-side confinement argument; the constants are deliberately loose, not an optimal capture bound.',
  KUTZ+'Implementation of Figure 3 with radius 100 and seven-site corner arms, rather than the illustrated constants.'),
 ('mono','angelWins_mono','Winning Angel strategies are monotone in power',
  '{p q : Nat} (hpq : p ≤ q) (h : AngelDevil.AngelWins p) : AngelDevil.AngelWins q',
  'For natural-number powers p ≤ q, if a single power-p Angel strategy survives against every Devil, then a power-q Angel has a winning strategy as well.\n\nThe game histories and Devil actions are unchanged when only the permitted jump radius increases.',
  MATHE+'Elementary consequence of the Chebyshev jump rule, not a separately numbered theorem.'),
 ('higher','power_ge_two_wins','Every Angel of integer power at least two wins',
  '(p : Nat) (hp : 2 ≤ p) : AngelDevil.AngelWins p',
  'For every integer power p ≥ 2, there exists one Angel strategy that survives forever against every ordinary Devil strategy on the infinite integer lattice.\n\nThe Devil burns at most one square per round; the convention is Devil first, with passing permitted. This is the monotonicity corollary of the power-two theorem.',
  MATHE+'Monotonicity corollary of Theorem 4.6.'),
 ('one','power_one_devil_wins','The Devil defeats the power-one Angel',
  ': ∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives 1 A D',
  'There exists a single ordinary Devil strategy that defeats every power-one Angel strategy on the infinite board. Defeat means a finite round with an illegal jump or a landing on an already burned square.\n\nThe quantifier order is one Devil strategy against all Angel strategies, not a separate opponent chosen after each Angel strategy. The model allows the Angel to stay still and the Devil to burn the occupied square; only subsequent landings lose.',
  KUTZ+'Berlekamp chess-king capture argument. Formal implementation uses 56 preparatory burns in a radius-100 box, followed by finite exhaustion; no optimal deadline claimed.'),
 ('classification','angelWins_iff_two_le','Complete classification by integer Angel power',
  '(p : Nat) : AngelDevil.AngelWins p ↔ 2 ≤ p',
  'In the standard infinite-board game against a Devil that burns at most one square per round, the Angel has a winning strategy exactly for natural-number powers p ≥ 2.\n\nThe negative cases are p=0 and p=1. The zero-power case is included because the formal parameter ranges over all natural numbers. This combines the known king-capture result with Mathe\'s power-two theorem and monotonicity.',
  KUTZ+MATHE+'Logical combination of these published results.')]
problems=[]
for key,name,title,typ,prose,source in specs:
    pre = 'import Definitions.Def_AngelDevil_KingGuard' if key in ['guard','box'] else 'import Definitions.Def_AngelDevil_Game'
    problem={'theorem_name':'AngelDevil.'+name,'theorem_title':title,
        'formal_statement':'theorem AngelDevil.'+name+' '+typ+' := by sorry',
        'preamble':pre,'natural_language_statement':prose,'source':source,
        'tags':['combinatorics','game-theory','angel-problem']}
    problems.append({'key':key,**problem})
    (ROOT/'Theorems'/('Thm_AngelDevil_'+name+'.lean')).write_text(pre+'\n'+problem['formal_statement']+'\n',encoding='utf-8')
(OUT/'problems.json').write_text(json.dumps(problems,indent=2),encoding='utf-8')
print('Prepared',len(problems),'proof packages and reference statements')
