# Status — 2026-10-19

- Research: complete integer-power classification, combining the published king-capture argument and Mathe 2007; no new mathematical result claimed.
- Classification: `AngelWins p ↔ 2 ≤ p`, **Proved**, `78319c36-be90-44b7-ae39-6f212616b326`.
- Power one: one Devil defeats every Angel strategy, **Proved**, `26888492-cdea-4b37-b3a2-327d25204e18`.
- Extension proofs: all six **ACCEPTED**; classification graph has 37 nodes, 66 edges, zero open leaves, and no unexpanded adjacency.
- Extension audit: [classification-audit.md](verification/classification-audit.md).
- Source: author manuscript downloaded; its checksum was reverified against `papers/source.json`.
- Local verification: 228 theorems checked on Lean 4.33.1, including the exact original targets; only standard axioms, no `sorryAx`.
- Main theorem: **Proved**, `6204cf5d-3e21-4e77-91ee-856e578b4253`.
- Platform graph: **zero open leaves**, with the Claim 4.2 → no-return → Theorem 4.5 → main path verified.
- Prove2Me proposal: `8632c949-8a1d-477d-b87b-ad737965860b`, **In review** after human submission; `mission_id: null`. Administrative moderation remains pending.
- Repository: https://github.com/Anchen-AI4Math/angel-devil (public, main).

## Original Mathe results (unchanged)

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
| Geometric no-return | `775a4edf-d28a-4a62-89b2-2c5de5c2feaf` | ACCEPTED |
| Original Theorem 4.5 | `880e0f8b-5ca9-4de7-965e-33979f37fbaf` | Proved by dependency closure |
| Original main Theorem 4.6 | `6204cf5d-3e21-4e77-91ee-856e578b4253` | Proved by dependency closure |

## Evidence and scope

The final geometric proof submission is
`52287fc3-ae4a-4382-a8cb-380bb94d7fd3` (**ACCEPTED**). It imports and uses
Claim 4.2. The existing reductions then close both original remaining targets.
`Solutions/Completed.lean` also assembles the full result locally without
importing platform placeholders. See `verification/completion-audit.md`.

The proof covers arbitrary Devil strategies under the original game definition,
not just finite boards or sampled plays. The explicit wall strategy is used
against Nice Devils; the unrestricted strategy is obtained by the proved
reduction. The definition of the game and the published wall strategy were
compared against the server and are unchanged.

No mathematical proof obligation remains for the original three targets.
Mission moderation is still pending and is not represented as completed.
Earlier increment audits are historical; the completion audit is authoritative
for the current proof and graph status. No new theorem or peer-reviewed
publication is claimed beyond formalizing the cited existing result.
