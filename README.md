# Angel–Devil: complete integer-power classification

Lean now proves `AngelWins p ↔ 2 ≤ p`: one Devil defeats every power-one
Angel, and every power at least two has a winning Angel strategy. The
[classification is Proved on Prove2Me](https://prove2.me/theorems/78319c36-be90-44b7-ae39-6f212616b326).

This combines the known Berlekamp king-capture argument, as presented in
[Kutz 2004, Section 1.1](https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf),
with the completed formalization of Andras Mathe, *The Angel of power 2 wins*,
Combinatorics, Probability and Computing 16 (2007), 363–374.
[Paper DOI](https://doi.org/10.1017/S0963548306008303).

**The original main theorem is Proved on Prove2Me and proved in the closed local
Lean library.** This formalizes a published result; it claims no new mathematical
solution and no independent peer review.

## Verified result

- `AngelDevil.power_one_devil_wins` — one Devil strategy defeats every power-one Angel.
- `AngelDevil.power_ge_two_wins` — every integer power at least two wins.
- `AngelDevil.angelWins_iff_two_le` — exact classification for all natural-number powers, including zero.
- `AngelDevil.devilWins_iff_le_one` — complementary classification in the closed local library.

- `AngelDevil.power_two_wins : AngelDevil.AngelWins 2` — one power-two strategy
  survives against every Devil in the original infinite-board game.
- `AngelDevil.power_two_beats_nice_devil : AngelDevil.NiceAngelWins 2` — one
  explicit strategy survives and escapes every finite box against every Nice Devil.
- The original Theorem 2.7 reduction is also proved, using finite-game
  determinacy, compactness, reduced journeys and confinement transfer.
- **228 local theorems** checked, with only `propext`, `Classical.choice` and
  `Quot.sound` in their axiom dependencies; no `sorryAx` or custom axioms.
- **Zero open leaves** in both the original theorem graph and the complete classification graph. All six extension proofs are ACCEPTED; the latter graph has 37 nodes and 66 edges. The geometric no-return
  proof is ACCEPTED and actually imports the proved Claim 4.2 perimeter bound.

[Classification audit](verification/classification-audit.md) · [Closed classification](Solutions/PowerClassification.lean)

[Original live main theorem](https://prove2.me/theorems/6204cf5d-3e21-4e77-91ee-856e578b4253)
· [Completion audit](verification/completion-audit.md)
· [Closed local assembly](Solutions/Completed.lean)

## Reproduce local checks

Install elan and the pinned Lean toolchain. From a fresh checkout, in PowerShell:

```powershell
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
lake update
lake exe cache get Mathlib.Combinatorics.Compactness Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Data.Fintype.Prod Mathlib.Data.Fintype.Fin Mathlib.Tactic.FinCases
python scripts/verify.py
```

Lean is pinned to `v4.33.1` and Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, matching the platform environment.
The verifier builds `Solutions.PowerClassification`, checks the exact types of
the original mission targets and the new classification, and audits the axioms
of the closed proof library.
It separately elaborates the original reference statements.

`Theorems/` contains platform statement mirrors with `sorry`, including mirrors
of results now proved on the server. These are excluded from the closed local
library. Files packaging platform reductions import those mirrors for protocol
compatibility; compiling such a package alone is not a closed local proof.
Use `Solutions.PowerClassification` and `scripts/verify.py` for the full closed
proof. `Solutions.Completed` remains the original power-two assembly.

## Proof route

For power one, a kernel-checked five-burn line-guard certificate supplies the
local barrier strategy. Preblocked corners let four guards confine the king
to a finite square. Burning a fresh square each round then forces finite
failure. The formal proof uses deliberately loose radius-100 constants; no
optimal capture time is claimed. See the [classification audit](verification/classification-audit.md).

The Nice strategy uses the paper's octagonal corner convention, with exactly
two wall transitions per turn. Each transition moves the outside square by at
most one king step. Nice protection preserves earlier empty squares, so the
first repeated wall would be the initial wall. A first contact with the x-axis
would yield a finite frozen boundary cycle whose lower length bound exceeds
the connected-component perimeter upper bound. Therefore no return occurs,
and a finite-box argument proves escape. Theorem 2.7 then gives the original
unrestricted Angel theorem. See [the geometric proof explanation](platform/no-return-explanation.md)
and [implementation/source comparison](verification/wall-source-comparison.md).

## Source, mission and publication

- [Source provenance and checksum](papers/source.json). The downloaded author
  manuscript is retained locally in `papers/`; PDF/text are not redistributed.
- [Source-to-model audit](verification/source-audit.md) and
  [original independent blind read-backs](verification/readbacks.json).
- [Local validation](verification/local-checks.json) and [current status](status.md).
- Prove2Me proposal `8632c949-8a1d-477d-b87b-ad737965860b` remains **In review**
  after human submission, with `mission_id: null`. Its published original
  theorem graph is complete; platform mission moderation is a separate process.

Formalization of already public work is public by default. Original mathematical
results must stay private until the owner explicitly authorizes publication.
