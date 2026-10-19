"""Check the closed library, original targets, and integer-power classification."""
from pathlib import Path
import subprocess
import json
import sys
import re
sys.stdout.reconfigure(encoding='utf-8')

root = Path(__file__).resolve().parents[1]
out = root / 'verification'
out.mkdir(exist_ok=True)
closed_modules = ['Foundation', 'Histories', 'ReducedJourney', 'NiceReduction', 'Confinement', 'FiniteHorizon', 'StrategyCompactness', 'FiniteDeterminacy', 'SquareBoundary', 'WallWalk', 'WallStrategy', 'WallGeometry', 'WallComponent', 'WallTruncation', 'WallNoReturn', 'Completed', 'KingGuard', 'KingGuardCertificate', 'KingBox', 'KingCapture', 'PowerClassification']
names = []
for module in closed_modules:
    source = (root/'Solutions'/(module+'.lean')).read_text(encoding='utf-8-sig')
    names.extend(re.findall(r'^theorem (\w+)', source, re.MULTILINE))
audit = root / 'tmp' / 'Audit.lean'
audit.parent.mkdir(exist_ok=True)
target_checks = '''
example (p : Nat) (hp : 0 < p) :
    ¬ AngelDevil.AngelWins p → ∃ N, 0 < N ∧ AngelDevil.NiceCanConfine p N :=
  AngelDevil.nice_devil_reduction p hp
example : AngelDevil.NiceAngelWins 2 := AngelDevil.power_two_beats_nice_devil
example : AngelDevil.AngelWins 2 := AngelDevil.power_two_wins
example : ∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives 1 A D := AngelDevil.power_one_devil_wins
example (p : Nat) : AngelDevil.AngelWins p ↔ 2 ≤ p := AngelDevil.angelWins_iff_two_le p
example (p : Nat) : (∃ D : AngelDevil.DevilStrategy, ∀ A, ¬ AngelDevil.Survives p A D) ↔ p ≤ 1 := AngelDevil.devilWins_iff_le_one p
'''
audit.write_text('import Solutions.PowerClassification\n' + target_checks + '\n'.join(
    '#print axioms AngelDevil.' + n for n in names) + '\n', encoding='utf-8')
commands = [('build', ['lake', 'build', 'Solutions.PowerClassification']),
            ('axioms', ['lake', 'env', 'lean', str(audit)]),
            ('open-target-elaboration', ['lake', 'env', 'lean', 'Theorems/PaperTargets.lean'])]
results = {}
for name, command in commands:
    proc = subprocess.run(command, cwd=root, capture_output=True, encoding='utf-8')
    text = proc.stdout + proc.stderr
    (out / (name + '.log')).write_text(text, encoding='utf-8')
    print(name, proc.returncode, text)
    if proc.returncode: raise SystemExit(proc.returncode)
    if name == 'axioms' and 'sorryAx' in text:
        raise SystemExit('Unexpected sorry dependency in proven code')
    if name == 'axioms':
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for group in re.findall(r'depends on axioms: \[([^\]]*)\]', text):
            actual = {item.strip() for item in group.split(',') if item.strip()}
            if not actual <= allowed:
                raise SystemExit('Unexpected axiom dependencies: '+repr(actual-allowed))
    results[name] = {'exit_code': proc.returncode}
results.update({'proved_foundation_theorems': names,
                'paper_targets_proved': True,
                'original_target_types_checked': ['nice_devil_reduction', 'power_two_beats_nice_devil', 'power_two_wins'],
                'paper_target_placeholders': 3,
                'classification_target_types_checked': ['power_one_devil_wins', 'angelWins_iff_two_le', 'devilWins_iff_le_one'],
                'classification_proved': True,
                'toolchain': (root/'lean-toolchain').read_text().strip()})
(out / 'local-checks.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
