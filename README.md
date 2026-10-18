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
- Seventy-four checked theorems. Claim 2.6, Theorem 2.4, uniform confinement,
  and the original Nice Devil reduction (Theorem 2.7) are proved.
- The remaining open milestone is power-two escape against Nice Devils
  (Theorem 4.5). Its geometric estimates and wall-following argument remain
  unproved; therefore the main result (Theorem 4.6) remains open.
- The Prove2Me proposal is **In review** after human submission. Its original
  theorem statements are published; Theorem 2.7 is now Proved. Open
  [Prove2Me](https://prove2.me), then **My missions**, and select
  **The Angel of Power 2 Wins (Mathe)**. Proposal ID:
  `8632c949-8a1d-477d-b87b-ad737965860b`.

## Reproduce local checks

Install elan and the pinned Lean toolchain. From a fresh checkout, in PowerShell:

```powershell
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
lake update
lake exe cache get Mathlib.Combinatorics.Compactness
python scripts/verify.py
```

Lean is pinned to `v4.33.1` and Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`, exactly matching the platform environment.
The strategy compactness proof uses Mathlib's Rado selection lemma.

The closed library is built through `Solutions.FiniteDeterminacy`; it contains
no `sorry` placeholders, imports no platform theorem placeholders, and has no
`sorryAx` in its printed axiom dependencies. `Theorems/` files are statement
reference mirrors and may contain `sorry` even for platform-proved results.
They are excluded from the closed-library audit. The main platform reduction
is checked separately; it remains incomplete while Theorem 4.5 is open.

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
milestones, one proved and one open. See [the live main theorem](https://prove2.me/theorems/6204cf5d-3e21-4e77-91ee-856e578b4253)
and [the recorded graph](verification/main-graph-after.json).

Claim 2.6, Theorem 2.4, finite-survival compactness, finite-game determinacy,
and uniform confinement have server verdict **ACCEPTED**. The original
Theorem 2.7 is **Proved** by dependency closure. The main graph now has one
open leaf: Theorem 4.5. See [current graph audit](verification/compactness-graph-audit.md).

## Publication convention

Formalization of already public work is public by default. Original mathematical
results must stay private until the owner explicitly authorizes publication.
