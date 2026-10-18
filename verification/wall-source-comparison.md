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

`wallTrace_never_returns` is the explicit remaining geometric obligation for
this implementation. It states nonreturn of the complete initial directed
wall, not nonreturn of the Angel's position and not the stronger assertion that
the green line never touches the x-axis. The intended geometric proof follows
the first-contact boundary count of Proposition 4.3; that proof has not been
completed, and this open statement must not be treated as an established
consequence merely because it resembles the paper's assertion.

`niceAngelWins_of_wall_no_return` has this obligation as an explicit hypothesis.
Its conclusion is the original `NiceAngelWins 2`, with one strategy working for
every Nice Devil. Its checked proof supplies the strategy, survival, persistence
of empty outside squares, first-repeat argument, and finite-box escape argument.
It does not assume these intermediate claims. The open geometric hypothesis is
kept as a separate child in the intended platform reduction, not concealed in
a definition or replaced by a finite experiment.
