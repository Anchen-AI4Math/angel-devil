# Boundary-counting increment — 2026-10-18

Historical increment snapshot. See [completion audit](completion-audit.md) for the current, closed proof status.

Mathe Claim 4.2 is now **Proved** on Prove2Me:

- Theorem: `595569d4-9682-4a6c-9967-8e47f242c4c0`.
- Proof: `700b1bdf-1d4f-4089-8f8e-7005b53c9d6e`, **ACCEPTED**.
- Definition bundle: `4391822a-6fe3-4195-bbb4-f998a5562061`.
- Server evidence: `boundary-proof-result.json`, `boundary-theorem-state.json`.
- Blind statement readback and source comparison: `boundary-readback.md`.

The closed local library checks 89 theorems, with no `sorryAx` in their axiom
dependencies. `Solutions/SquareBoundary.lean` adds 15 theorems. It proves the
gluing characterization needed for the perimeter bound, the loss of an old
boundary side when a neighboring square is added, and an explicit finite set
of occupied-square/direction walls whose cardinality equals the perimeter.
Any subset of these distinct boundary walls inherits the same upper bound.
All boundaries of holes are included.

## Scope and remaining work

`boundary-main-graph.json` still shows the original main theorem Open and
Theorem 4.5 Open. Claim 4.2 is currently a standalone proved helper, not an
imported node of a verified Theorem 4.5 reduction. No graph edge is claimed
merely because a lemma will be useful later.

The remaining geometric obligations include constructing the directed runner,
showing that its painted walls do not repeat, proving at least two walls of
progress per turn, proving connectedness of the relevant occupied supports,
and establishing the first-return length estimate and unbounded escape.
The arithmetic contradiction already in Foundation does not prove any of
these geometric hypotheses.

The proposal remains **In review**, with `mission_id: null`, as recorded in
`boundary-proposal-state.json`. This increment formalizes a published lemma;
it does not claim original mathematics or completion of the mission.
