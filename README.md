# The Angel of Power 2 Wins — Lean formalization

Formalization in progress of Andras Mathe, *The Angel of power 2 wins*,
Combinatorics, Probability and Computing 16 (2007), 363–374.
[Paper DOI](https://doi.org/10.1017/S0963548306008303).

**The main theorem is not yet proved in this repository.** This project formalizes
an already published mathematical result; it claims no new mathematical solution.

## Current increment

- An explicit infinite integer-board game with Devil-first rounds, passes,
  history-dependent strategies, survival, Nice Devils, escape, and finite-prefix
  confinement.
- Forty-two checked foundational and finite-journey lemmas, including the final arithmetic contradiction
  used in Proposition 4.3 and a conditional assembly of the two paper milestones.
  The geometric estimates and the two milestones themselves remain unproved.
- Three open statements: the Nice Devil reduction (Theorem 2.7, including the
  introductory determinacy observation), Nice Devil escape (Theorem 4.5), and
  the main result (Theorem 4.6).
- The Prove2Me proposal is **In review** after human submission. Its three
  theorem statements are published and still Open. Open
  [Prove2Me](https://prove2.me), then **My missions**, and select
  **The Angel of Power 2 Wins (Mathe)**. Proposal ID:
  `8632c949-8a1d-477d-b87b-ad737965860b`.

## Reproduce local checks

Install elan and the pinned Lean toolchain, then run:

```sh
python scripts/verify.py
```

The initial library uses `Std`, with no external package dependency. Lean is
pinned to `v4.33.1`; the proposal targets the platform's Mathlib environment
`0df444a360eaa60ab8c11dca51a86af692955474`. Introducing Mathlib later must preserve
that pin or deliberately migrate the proposal.

The closed library (`Foundation`, `Histories`, `ReducedJourney`, `NiceReduction`) contains no
`sorry` placeholders and imports no open theorem statements. The axiom report contains no `sorryAx`. `Theorems/PaperTargets.lean`
contains **three explicit `sorry` placeholders** and is checked separately for
statement elaboration only. `Solutions/MainReduction.lean` is checked separately: the platform accepted it
as `SKETCH_ACCEPTED`, with two open milestone dependencies. It is not a closed proof.

## Source and audit

- [Source provenance and checksum](papers/source.json). The downloaded author
  manuscript is retained locally in `papers/`; its PDF/text are not redistributed
  in this repository.
- [Source-to-model audit](verification/source-audit.md).
- [Independent blind read-backs](verification/readbacks.json).
- [Local validation results](verification/local-checks.json).
- [Status and next steps](status.md).
- [Mission proposal description](platform/proposal-description.md).

The proposal has four items and two milestones. Human submission is complete;
moderation is pending. The main theorem now has a verified reduction to its two
open milestones. See [the live main theorem](https://prove2.me/theorems/6204cf5d-3e21-4e77-91ee-856e578b4253)
and [the recorded graph](verification/main-graph-after.json).

The earliest-predecessor reduction now preserves valid finite journeys in Lean.
This is structural groundwork for Claim 2.6, not yet its assertion about eaten
squares under the transformed Devil. The finite-prefix correspondence, strategy
reduction, determinacy argument and geometric escape proof remain to be completed.

## Publication convention

Formalization of already public work is public by default. Original mathematical
results must stay private until the owner explicitly authorizes publication.

The reduced-journey preservation theorem has server verdict `ACCEPTED` (submission
`b5e68d92-4b5a-41c1-bd2c-27a41a0c3b4d`); see
[verdict](verification/reduced-journey-verdict.json). This independent structural
lemma is not yet connected to the main graph. Additional local proofs establish
order-preserving deletion, the Nice property of equation (2), and the bridge from
safe play prefixes to allowed finite journeys. Claim 2.6 itself remains open.
