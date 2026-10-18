# Wall strategy and geometric frontier — 2026-10-18

Historical increment snapshot. See [completion audit](completion-audit.md) for the current, closed proof status.

## Verified proof and reduction

| Item | ID | Status |
|---|---|---|
| Wall-walk definitions | `778bd072-6fcb-407d-85d0-a013477fb67c` | Published |
| No-return implies NiceAngelWins 2 | `3ec0f8c7-bca2-454f-9f1f-e43728a98359` | Proved |
| Conditional proof submission | `05d1a48d-8270-4a2a-ad1a-2c0319e2d981` | ACCEPTED |
| Original Theorem 4.5 reduction | `b8f1dd37-d9a2-4dec-8cd8-df14d87cadd5` | SKETCH_ACCEPTED |
| Geometric no-return child | `775a4edf-d28a-4a62-89b2-2c5de5c2feaf` | Open |

The local closed library now checks **123 theorems**. The 34 additions include
successor legality, a predecessor invariant under growing obstacles, the actual
history-based wall strategy's survival, persistent protection of intermediate
squares, first-repeat-at-initial-wall, and escape conditional on no return.
The axiom audit excludes `sorryAx`. `wall-source-hashes.json` pins the submitted
implementation and proof package. The complete conditional proof imports only
published definitions and Mathlib, not its target or any open theorem.

`Solutions/WallMilestoneReduction.lean` is deliberately separate: it imports
the conditional theorem and the **open** no-return theorem. Compiling this
reduction is not evidence that no-return is proved. The reference modules in
`Theorems/` contain platform statement placeholders and are excluded from the
closed-library axiom audit.

## Graph readback

`wall-main-graph-after.json` contains both full paths:

1. Conditional theorem → `sketch-b8f1dd37-d9a2-4dec-8cd8-df14d87cadd5`
   → original Theorem 4.5 (`880e0f8b-5ca9-4de7-965e-33979f37fbaf`).
2. Geometric no-return → the same sketch → original Theorem 4.5.

Theorem 4.5 remains connected through the original main reduction
`a7e909c2-b877-43ef-86cf-e400407b697f` to the original main theorem
`6204cf5d-3e21-4e77-91ee-856e578b4253`. Both remain **Open**.
No graph node reports unexpanded parents or children.
`wall-main-open-leaves.json` reports exactly one open leaf: geometric no-return.
`wall-nice-decompositions-after.json` records the actual two-child reduction.

Claim 4.2 remains a separately proved helper. The present conditional proof
does not use it, and no artificial graph edge to it has been added. Its intended
use is in the still-missing geometric no-return proof.

## Source fidelity and limits

The implementation follows the paper's octagonal corner rule and truncates
each turn to two wall transitions, each moving the outside square by at most
one king step. It does not claim to implement the maximal per-turn path.
The exact statements were read back independently in `wall-readback.md`;
the comparison with the paper and this implementation choice are explained in
`wall-source-comparison.md`.

The remaining work is the first-contact geometry and finite obstacle boundary
count proving no return. This is not supplied by the proved conditional theorem.
The proposal remains **In review**, with `mission_id: null`, as freshly checked
in `wall-proposal-state.json`. The mission and original main theorem are not
complete; no new mathematical result is claimed.
