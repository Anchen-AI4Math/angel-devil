# Status — 2026-10-18

- Research: formalization of Mathe's published 2007 theorem; no new mathematical result claimed.
- Source: author manuscript downloaded; checksum in `papers/source.json`.
- Local verification: 52 lemmas compile on Lean 4.33.1 without `sorryAx` in their axiom dependencies.
- Prove2Me proposal: `8632c949-8a1d-477d-b87b-ad737965860b`, In review after human submission; moderation pending.
- Main theorem: **open**, `6204cf5d-3e21-4e77-91ee-856e578b4253`.
- Repository: https://github.com/Anchen-AI4Math/angel-devil (public, main).

## Verified Section 2 results

| Result | Theorem ID | Server proof |
|---|---|---|
| Reduced journeys preserve Journey | `09953273-0806-4e9f-a1da-0b10a2292ffb` | ACCEPTED |
| Claim 2.6: preservation of Allowed | `b6f4b8fc-c1fe-4fc7-a690-ba558187e1e5` | ACCEPTED |
| Theorem 2.4: confinement transfer | `573ba228-d8a4-41f7-ab55-9aad2fd7f68d` | ACCEPTED |

Theorem 2.4 uses Claim 2.6, which uses the reduced-journey preservation theorem.
Theorem 2.7 has an accepted sketch using Theorem 2.4 and the still-open uniform
confinement theorem. All of these edges were read back from the platform;
see `verification/section2-graph-audit.md`. The local closed library also proves
these statements independently without importing platform placeholders.

## Remaining open leaves

1. `AngelDevil.uniform_confinement` (`2202ef8d-e4d0-4b0b-81af-3c0549e73536`):
   positive-power determinacy/compactness and a single finite confinement box.
2. `AngelDevil.power_two_beats_nice_devil` (`880e0f8b-5ca9-4de7-965e-33979f37fbaf`):
   Claim 4.2, the wall-following strategy, and the escape proof of Theorem 4.5.

The main reduction and Theorem 2.7 reduction have status SKETCH_ACCEPTED, not
closed proofs. Full completion requires both remaining leaves to be proved and
the original main theorem and its graph to be verified closed.
