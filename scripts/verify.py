"""Build proved code, inspect axioms, then separately elaborate open targets."""
from pathlib import Path
import subprocess
import json
import sys
sys.stdout.reconfigure(encoding='utf-8')

root = Path(__file__).resolve().parents[1]
out = root / 'verification'
out.mkdir(exist_ok=True)
names = ['jump_self', 'jump_mono', 'jump_symm', 'jump_add', 'play_lengths',
         'pass_is_nice', 'wall_budget_contradiction',
         'nice_wins_excludes_confinement', 'nice_escape_and_reduction_imply_win']
audit = root / 'tmp' / 'Audit.lean'
audit.parent.mkdir(exist_ok=True)
audit.write_text('import Solutions.Foundation\n' + '\n'.join(
    '#print axioms AngelDevil.' + n for n in names) + '\n', encoding='utf-8')
commands = [('build', ['lake', 'build', 'Solutions.Foundation']),
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
    results[name] = {'exit_code': proc.returncode}
results.update({'proved_foundation_theorems': names,
                'paper_targets_proved': False,
                'paper_target_placeholders': 3,
                'toolchain': (root/'lean-toolchain').read_text().strip()})
(out / 'local-checks.json').write_text(json.dumps(results, indent=2), encoding='utf-8')
