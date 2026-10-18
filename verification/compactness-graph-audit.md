# Compactness branch audit — 2026-10-18

The exact original Theorem 2.7 (`76719177-828c-4447-b573-06ec5a9f0684`)
now has platform status **Proved**. The original main theorem
(`6204cf5d-3e21-4e77-91ee-856e578b4253`) remains **Open**.

| Result | Proof submission | Verdict |
|---|---|---|
| Finite-survival compactness | `eea2d952-0175-46ea-9bfd-7196e1130416` | ACCEPTED |
| Finite-game determinacy | `3d322903-a7e1-4217-862a-3e6127177f79` | ACCEPTED |
| Uniform confinement | `e9b369e4-3a61-4f2c-b56b-9dcfcc9f18c0` | ACCEPTED |

The uniform confinement submission actually uses the compactness theorem
`9ce68653-543f-4f54-ad03-38a632ec30d1` and finite-determinacy theorem
`755f9736-9c48-4e56-a844-ee7810ff855b`. The main graph contains both
child → submission → uniform-confinement paths. Uniform confinement and
Theorem 2.4 are the two proved children of the previously accepted Theorem 2.7
reduction (`9650a163-653b-4113-bb8b-d051cf03f583`).

Current evidence is in `main-graph-after.json`, `nice-milestone-graph-after.json`,
`uniform-confinement-graph-after.json` and their decomposition responses.
No main-graph node reports unexplored children or parents. Definitions used
only inside direct proof implementations are not asserted to be theorem edges.

`main-open-leaves-after.json` reports exactly one open leaf:
`880e0f8b-5ca9-4de7-965e-33979f37fbaf`, Theorem 4.5 (power-two Nice escape).
The geometric proof is not yet complete. No claim of a completed main theorem
or completed mission follows from closing the Section 2 branch.

The independent local build contains 74 checked theorems, including the exact
original `uniform_confinement` and `nice_devil_reduction` statements. Their
printed axiom dependencies are only `propext`, `Classical.choice`, `Quot.sound`;
there is no `sorryAx`. This build excludes all platform statement mirrors.
Mathlib's Rado selection lemma is used at the mission's exact pinned revision.
