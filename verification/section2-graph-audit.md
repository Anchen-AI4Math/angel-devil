# Section 2 proof and dependency audit — 2026-10-18

The initial Section 2 increment built with 52 declarations and no `sorryAx` in the
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

At this initial audit there were two open leaves: uniform confinement and
power-two escape. Uniform confinement has since been proved and the original
Theorem 2.7 closed. The graph JSON files are refreshed to the latest state;
see `compactness-graph-audit.md` for the current one-leaf frontier. The main
theorem remains Open pending Theorem 4.5.
