# Section 2 proof and dependency audit — 2026-10-18

The closed local library builds with 52 declarations and no `sorryAx` in the
printed axiom dependencies. Platform reference modules remain placeholders and
are deliberately excluded from this closed-library audit.

| Parent | Submission | Verdict | Actual theorem children |
|---|---|---|---|
| Main theorem | `a7e909c2-b877-43ef-86cf-e400407b697f` | SKETCH_ACCEPTED | Theorem 2.7; Theorem 4.5 |
| Theorem 2.7 | `9650a163-653b-4113-bb8b-d051cf03f583` | SKETCH_ACCEPTED | uniform confinement; Theorem 2.4 |
| Theorem 2.4 | `42cf9ad1-e809-4fe5-8895-07f5d7aa31c4` | ACCEPTED | Claim 2.6 |
| Claim 2.6 | `97eeb292-fd7e-40ce-9b4b-c045518e225a` | ACCEPTED | reduced journeys preserve Journey |

The `main-graph-after.json` response includes each child → submission → parent
path, and the corresponding `*-decompositions-after.json` files independently
identify the children. No node reports unexplored children or parents. The
accepted Claim 2.6 and Theorem 2.4 submissions also import the actual NiceReduction
definition; these definition edges do not represent unresolved mathematical work.

`main-open-leaves-after.json` reports exactly two open leaves:

- `2202ef8d-e4d0-4b0b-81af-3c0549e73536`: uniform confinement, including determinacy.
- `880e0f8b-5ca9-4de7-965e-33979f37fbaf`: power-two escape against Nice Devils.

The original main theorem is still Open. A connected verified partial graph does
not establish either remaining result or completion of the mission.
