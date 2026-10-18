# Completion audit — 2026-10-18

The original requested theorem formalization is complete. The platform mission
proposal's administrative moderation remains pending; it is not described as
an approved or launched mission.

## Original targets and server evidence

| Original target | Platform ID | Current status |
|---|---|---|
| Theorem 2.7, Nice Devil reduction | `76719177-828c-4447-b573-06ec5a9f0684` | Proved |
| Theorem 4.5, power two escapes Nice Devils | `880e0f8b-5ca9-4de7-965e-33979f37fbaf` | Proved |
| Theorem 4.6, power two wins | `6204cf5d-3e21-4e77-91ee-856e578b4253` | Proved |

The final geometric submission `52287fc3-ae4a-4382-a8cb-380bb94d7fd3` is
**ACCEPTED**. It proves the existing no-return child
`775a4edf-d28a-4a62-89b2-2c5de5c2feaf`; its exact published statement was
compared before submission and was not replaced or weakened. The three
original remote statements were also compared with `Theorems/PaperTargets.lean`.
Evidence: `no-return-proof-result.json`, `completion-*-state.json`, and
`completion-checks.json`.

The published Game and WallWalk definition bodies match the local files
(normalized line endings). The corresponding definition checks and source
SHA-256 values are recorded in `completion-game-definition-check.json`,
`completion-wallwalk-definition-check.json` and `completion-source-hashes.json`.

## Closed local proof

`Solutions/Completed.lean` imports the proved implementations, not the platform
statement mirrors. It establishes the exact conclusions:

```lean
AngelDevil.power_two_beats_nice_devil : AngelDevil.NiceAngelWins 2
AngelDevil.power_two_wins : AngelDevil.AngelWins 2
```

`python scripts/verify.py` successfully builds `Solutions.Completed`, checks
the exact types of all three original targets using explicit Lean examples,
and prints the axioms of all **185** local theorems. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The verifier rejects `sorryAx` and
any other axiom name. Evidence: `local-checks.json`, `build.log`, `axioms.log`.
Lean is `v4.33.1`; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`, matching the server environment.

`Theorems/` files remain statement mirrors with placeholders, even for proved
server results. Their separate elaboration is not counted as a proof.
Likewise, compiling a platform submission that imports a statement mirror is
not the closed-library check. The independent local implementation supplies
the proofs of its dependencies.

## Actual dependency graph

The fresh depth-10 main graph has 25 nodes and 38 edges, with no warning or
unexpanded parent/child flags. All theorem nodes are Proved (definition nodes
retain status Definition). The open-leaf endpoint reports **total 0**.
Evidence: `completion-main-graph.json`, `completion-main-open-leaves.json`.

The following full path is verified from the actual edge records:

1. Claim 4.2 (`595569d4-9682-4a6c-9967-8e47f242c4c0`)
   → submission `52287fc3-ae4a-4382-a8cb-380bb94d7fd3`
   → geometric no-return (`775a4edf-d28a-4a62-89b2-2c5de5c2feaf`).
2. No-return → submission `b8f1dd37-d9a2-4dec-8cd8-df14d87cadd5`
   → original Theorem 4.5. That submission also uses the proved
   no-return-to-winning implication (`3ec0f8c7-bca2-454f-9f1f-e43728a98359`).
3. Theorem 4.5 → submission `a7e909c2-b877-43ef-86cf-e400407b697f`
   → original main theorem. The same reduction uses the proved original
   Theorem 2.7 branch.

Claim 4.2 is now an actual dependency, rather than the formerly standalone
helper. Older SKETCH_ACCEPTED receipts are historical submission verdicts;
their child theorems are now all proved and the original parents are Proved.

## Source fidelity and delivered scope

- The author manuscript PDF is present locally and its SHA-256 was rechecked
  against `papers/source.json`. The PDF is not redistributed in the repository.
- The source result is Mathe 2007, DOI `10.1017/S0963548306008303`. Original
  statement readbacks and the wall-strategy readback remain in `verification/`.
- The proof covers the infinite integer board and arbitrary original Devil
  strategies, not a finite search or sampled play. Nice escape uses one
  history-based strategy for all Nice Devils, with every intermediate square's
  protection proved from the original Nice definition.
- The implementation uses two wall transitions per round under the paper's
  octagonal convention. It does not claim to take a maximal route each turn.
  The actual implementation's geometric no-return is now proved, including
  freezing/truncation, finite cycles, connected components, the column-top
  visit, and the lower and upper boundary-length estimates. See
  `wall-source-comparison.md` and `platform/no-return-explanation.md`.
- Work remains in the independent `math/angel-devil` topic repository, with
  public repository `Anchen-AI4Math/angel-devil` as authorized. No original
  mathematical result or independent peer review is claimed.
- Proposal `8632c949-8a1d-477d-b87b-ad737965860b` is still **In review** after
  human submission, with `mission_id: null` (`completion-proposal-state.json`).
  This is an administrative status separate from the completed theorem graph.

No mathematical proof obligation remains for the original target scope.
