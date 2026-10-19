## Motivation

The Angel problem asks whether bounded movement can overcome an adversary that destroys one square per turn on an infinite chessboard. It is a question about strategies for arbitrarily long play, rather than about finding a path through one fixed configuration. The Devil may act anywhere on the board, including far ahead of the Angel. The movement range therefore has to be compared with a changing obstacle set and with an opponent that observes earlier moves.

This mission collects the complete classification for natural-number powers in one formal development. The power-one loss is the known Berlekamp king-capture result described in [Kutz's 2004 thesis, Section 1.1](https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf). The power-two win is [Mathe's Theorem 4.6 (2007)](https://doi.org/10.1017/S0963548306008303). Higher powers and the exact threshold are consequences of these published results and the movement rules. This is formalization of known mathematics; it does not propose a new solution to an open problem.

## Setting

A **square** is a point of the integer lattice $\mathbb Z^2$. The Angel starts at the origin. Its **power** is a natural number $p$, including zero. A legal jump changes each coordinate by at most $p$ in absolute value. Intermediate squares impose no restriction, and zero-length moves are allowed. Thus power one has the movement range of a chess king, while power zero cannot change position.

The ordinary **Devil** moves first in every round. It chooses at most one square to burn, or passes. A burned square remains burned. Repeated choices are allowed and do not destroy additional squares. Naming the Angel's currently occupied square is permitted; the loss condition is checked at the Angel's subsequent landing. The Angel loses if its destination is burned or its displacement exceeds its power.

A **strategy** uses only the finite history available at the time of the move. A Devil strategy receives the visited positions. An Angel strategy receives these positions and the Devil actions, including the action just taken in the current round. Every pair of strategies defines a play by recursion. Write $\operatorname{Survives}(p,A,D)$ when all rounds of this play have legal, unburned landings, and define

$$\operatorname{AngelWins}(p)\;\Longleftrightarrow\;\exists A\;\forall D,\ \operatorname{Survives}(p,A,D).$$

## Formalization targets

The mission's main theorem is the exact classification

$$\forall p\in\mathbb N,\qquad \operatorname{AngelWins}(p)\;\Longleftrightarrow\;2\le p.$$

Its two principal outcomes are

$$\exists D\;\forall A,\quad \neg\operatorname{Survives}(1,A,D),$$

and

$$\forall p\in\mathbb N,\quad 2\le p\ \Longrightarrow\ \operatorname{AngelWins}(p).$$

The first statement supplies one Devil strategy defeating every power-one Angel, rather than an opponent chosen separately after seeing a complete Angel play. Likewise, the Angel's winning strategy is chosen before the opposing Devil strategy. All these statements use the same game definition.

The source milestones retain the original Nice Devil reduction and escape theorem, add Mathe's power-two theorem explicitly, and include the king-capture result from Kutz Section 1.1. A **Nice Devil** protects the origin and every square within movement range of any visited position other than the most recent position. The corresponding Angel objective includes leaving every finite box. This restricted opponent is an intermediate target; the headline classification concerns the ordinary, unrestricted Devil. Monotonicity and the higher-power corollary are available in the linked theorem dependency graph without attributing invented theorem numbers to either source.

## Significance

The classification identifies the exact integer threshold: one square of movement in each coordinate is insufficient, whereas two suffice. It distinguishes unlimited survival from success for a fixed number of rounds. The lower endpoint is covered as well, because the formal parameter is a natural number rather than a strictly positive integer.

The formal development makes the quantifier order, observation rules, and geometric assumptions inspectable. The classification and both principal outcomes already have machine-checked proofs. The [repository audit](https://github.com/Anchen-AI4Math/angel-devil/blob/main/verification/classification-audit.md) records 228 checked local theorems and six accepted extension submissions. Its classification dependency graph contains 37 nodes, 66 edges, and zero open leaves. These are verification results, not independent peer review or a new mathematical publication. The mission now presents this completed body of work as one navigable result.

## Difficulty

A finite simulation cannot establish survival against every opponent forever. Conversely, failure of several candidate Angel strategies does not establish a uniform winning Devil strategy. Finite and infinite play must be related without reversing the strategic quantifiers. The geometric statements also have to constrain the evolving play, rather than describe only a static drawing. For the king-capture result, local boundary restrictions must remain valid after every legal move; for the power-two result, the source's confinement and escape assertions must refer to the same operational game.

## Formalization scope

The implementation uses integer pairs, finite histories, optional Devil actions, finite sets, and recursion on natural numbers. Lean 4.33.1 and the pinned Mathlib revision match the platform environment. The closed local entry point is `Solutions.PowerClassification`; `Solutions.Completed` retains the original Mathe assembly. The definitions do not assume a winning strategy or restrict the headline game to a finite board.

The king-capture implementation uses deliberately loose radius-100 constants for an internal confinement argument. It does not claim an optimal capture time or a formalization of the smallest board illustrated by the source. Fractional speeds and Devils burning multiple squares per turn are outside this mission. Reusable material includes finite-game determinacy, finite-survival compactness, journey reduction, connected-square boundary estimates, and strategy monotonicity. Independent reproduction and documentation improvements are welcome; there is no remaining open proof obligation for the stated classification. Platform reference mirrors containing `sorry` are kept separate from the closed local proof library, whose audited dependencies contain only the standard Lean axioms.

## Selected references

- Martin Kutz, *The Angel Problem, Positional Games, and Digraph Roots*, PhD thesis, Saarland University, 2004, Chapter 1, Section 1.1, pages 2–3, Figures 1–3. [Thesis](https://people.mpi-inf.mpg.de/alumni/d1/2009/mkutz/diss/kutz_angel.pdf).
- Andras Mathe, *The Angel of power 2 wins*, Combinatorics, Probability and Computing 16 (2007), 363–374, Theorems 2.7, 4.5 and 4.6. [DOI](https://doi.org/10.1017/S0963548306008303).
