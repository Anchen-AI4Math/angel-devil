# Status — 2026-10-18

- Research: formalization of Mathe's published 2007 theorem; no new mathematical result claimed.
- Source: author manuscript downloaded; checksum in `papers/source.json`.
- Local verification: 123 theorems compile on Lean 4.33.1 without `sorryAx` in their axiom dependencies.
- Prove2Me proposal: `8632c949-8a1d-477d-b87b-ad737965860b`, In review after human submission; moderation pending.
- Main theorem: **open**, `6204cf5d-3e21-4e77-91ee-856e578b4253`.
- Repository: https://github.com/Anchen-AI4Math/angel-devil (public, main).

## Verified results

| Result | Theorem ID | Server proof |
|---|---|---|
| Reduced journeys preserve Journey | `09953273-0806-4e9f-a1da-0b10a2292ffb` | ACCEPTED |
| Claim 2.6: preservation of Allowed | `b6f4b8fc-c1fe-4fc7-a690-ba558187e1e5` | ACCEPTED |
| Theorem 2.4: confinement transfer | `573ba228-d8a4-41f7-ab55-9aad2fd7f68d` | ACCEPTED |
| Finite-survival compactness | `9ce68653-543f-4f54-ad03-38a632ec30d1` | ACCEPTED |
| Finite-game determinacy | `755f9736-9c48-4e56-a844-ee7810ff855b` | ACCEPTED |
| Uniform confinement | `2202ef8d-e4d0-4b0b-81af-3c0549e73536` | ACCEPTED |
| Claim 4.2: connected-square boundary | `595569d4-9682-4a6c-9967-8e47f242c4c0` | ACCEPTED |
| No-return implies NiceAngelWins 2 | `3ec0f8c7-bca2-454f-9f1f-e43728a98359` | ACCEPTED (conditional theorem) |
| Original Theorem 2.7 | `76719177-828c-4447-b573-06ec5a9f0684` | Proved by dependency closure |


Theorem 2.7's two children, uniform confinement and Theorem 2.4, are both
Proved. Uniform confinement actually imports the proved compactness and finite
strategic determinacy nodes. The entire branch is connected to the main target;
see `verification/compactness-graph-audit.md`. The new geometric lemma and
its earlier graph boundary are documented in `verification/boundary-audit.md`.
The current wall-strategy reduction is in `verification/wall-graph-audit.md`. The closed local library also
proves the exact Theorem 2.7 statement without importing platform placeholders.

## Geometric frontier

The explicit wall strategy has been implemented in the original history-based
interface. Its local proof establishes survival against every Nice Devil,
permanent protection of intermediate outside squares, and the first-repeat
property. It also proves that nonreturn of the initial directed wall implies
injectivity of the trace and escape from every finite box.

The remaining geometric obligation is `AngelDevil.wallTrace_never_returns`
(`775a4edf-d28a-4a62-89b2-2c5de5c2feaf`): for every Nice Devil and every positive
wall index, the specified trace differs from its initial wall. This is still
open. Its conditional implication is ACCEPTED, and the original Theorem 4.5
reduction is SKETCH_ACCEPTED with the verified no-return child edge. The main
graph has exactly this one open leaf. Theorem 4.5 and the main theorem remain open.

Claim 4.2 remains a separately proved perimeter lemma. It has not yet been used
in a verified no-return proof, so no dependency edge from it to no-return is
claimed. See `verification/wall-source-comparison.md` for the precise two-wall
implementation and its relation to the paper.

## Next work

Prove the geometric no-return statement using the first x-axis contact argument:
formalize directed wall endpoints, freeze and truncate the obstacle set, build
the finite boundary continuation, prove its length lower bound, and use the
connected-square perimeter bound and the Devil's one-square-per-turn budget.
Do not assume any of these missing geometric estimates. Then re-read the main
graph and verify closure through the original Theorems 4.5 and 4.6.
