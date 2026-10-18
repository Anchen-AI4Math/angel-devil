# Status — 2026-10-18

- Research: formalization of Mathe's published 2007 theorem; no new mathematical result claimed.
- Source: author manuscript downloaded; checksum in `papers/source.json`.
- Local verification: 74 theorems compile on Lean 4.33.1 without `sorryAx` in their axiom dependencies.
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
| Original Theorem 2.7 | `76719177-828c-4447-b573-06ec5a9f0684` | Proved by dependency closure |


Theorem 2.7's two children, uniform confinement and Theorem 2.4, are both
Proved. Uniform confinement actually imports the proved compactness and finite
strategic determinacy nodes. The entire branch is connected to the main target;
see `verification/compactness-graph-audit.md`. The closed local library also
proves the exact Theorem 2.7 statement without importing platform placeholders.

## Remaining open leaf

`AngelDevil.power_two_beats_nice_devil` (`880e0f8b-5ca9-4de7-965e-33979f37fbaf`):
Claim 4.2, the wall-following strategy, and the escape proof of Theorem 4.5.
The main theorem remains Open. Its original reduction was SKETCH_ACCEPTED;
that does not establish the remaining geometric milestone.

## Next work

Formalize the connected-square boundary bound, the runner's directed boundary
walk, non-repetition and progress estimates, and the resulting unbounded escape
strategy. Preserve the original power-two target and its universal quantification
over Nice Devils. Re-read the main graph and verify closure after that proof.
