The proof constructs one history-based Angel strategy. Its obstacle set is the
pre-eaten left half-plane together with the recorded Devil choices. A wall is
an occupied square and an outward normal, with its outside square as the Angel
position. The successor follows the shrunken-block convention: an empty tangent
neighbor takes priority, allowing passage between diagonally touching blocks.

Every successor remains a boundary wall and moves its outside square by at
most one king step. Two successors therefore form a legal power-two move.
Induction on the original game's rounds proves survival against every Nice
Devil; the old endpoint cannot be eaten, and the two intermediate transitions
remain within the original move's radius. All strategy outputs are reconstructed
from the chronological burn history, so no additional state interface is assumed.

A predecessor calculation gives a left inverse for the wall successor. It
remains valid as obstacles grow provided the earlier outside square stays empty.
Nice protection guarantees this persistence for the actual wall trace: each
intermediate outside square is within two of that round's starting position.
If the first repeated wall were not the initial one, taking predecessors would
give an earlier repeated pair. Hence the explicit no-return hypothesis implies
injectivity of the wall trace.

Finally, if Angel endpoints stayed in a box of radius N, all intermediate
outside squares would stay in radius N+2. An outside square and one of four
normal directions uniquely determine a wall. Encoding these pairs in a finite
type contradicts injectivity of the infinite trace. This proves unbounded
escape and combines it with survival to establish the exact NiceAngelWins 2
target. The geometric no-return premise remains an unproved input; neither
survival nor this conditional implication is a proof of that premise.
