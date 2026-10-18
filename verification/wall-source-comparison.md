# Wall-walk source comparison

Source: Mathe, author manuscript pp. 6-8. The independent literal readback is
in `wall-readback.md`; this document is the main agent's comparison with the
paper and is not part of that blind readback.

The outward normal points from an eaten square to the Angel's square. Rotating
it counterclockwise gives the direction of travel, with the eaten square on
the left. The successor tests the tangent-side square before the diagonal
square. This is the octagonal convention of Figure 3: when only the diagonal
square is occupied, the Angel squeezes through the corner gap and follows the
same occupied square. A standard square-maze successor with the opposite test
priority would not formalize this rule.

The implementation makes exactly two wall transitions per turn. This is an
admissible truncation of the paper's walk: each transition changes the outside
square by at most one king step, so both intermediate and final positions lie
within power two of the starting square, using at most two path steps and two
painted walls. The paper allows up to four steps/walls and uses the lower bound
of two painted walls per turn. We do not assert that the implementation takes
the paper's maximal possible route each turn. Its survival, protection, and
conditional escape properties are independently proved for this exact rule.

`wallTrace_never_returns` states nonreturn of the complete initial directed
wall. It is now proved by `Solutions/WallNoReturn.lean`, through the stronger
positive-height invariant for every positive-index wall start. The proof uses
the first-contact boundary count of Proposition 4.3 for this exact strategy;
it does not infer correctness merely from resemblance to the paper.

The finite truncation retains the pre-eaten column and the recorded nonnegative
quadrant burns. The wall orbit stays in one side-connected component, which
permits the proved Claim 4.2 bound even if unrelated obstacles are disconnected.
The column's top wall lies in the initial cycle by an explicit return path and
injectivity. Two coordinate potentials prove the lower length count. The
resulting contradiction rules out first contact with the x-axis.

`niceAngelWins_of_wall_no_return` retains this condition as an explicit
hypothesis, now discharged by the separate proved child. Its conclusion is the
original `NiceAngelWins 2`, with one strategy working for every Nice Devil.
The main theorem then follows through the original Theorem 2.7 reduction.
See `completion-audit.md` for closed local and server evidence.
