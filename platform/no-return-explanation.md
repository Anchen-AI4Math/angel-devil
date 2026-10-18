We prove the stronger invariant that the initial vertex of every positive-index
wall has strictly positive second coordinate. Suppose instead that index j is
the first nonpositive vertex. The first segment points north from the origin,
so j is greater than one. The incoming wall must point downwards: its occupied
square is (x,0), its outward normal is west, and its outside square has first
coordinate x-1. Since the negative half-plane is pre-eaten, x is at least one.

Freeze after the Devil move used by the last segment, at round
t = floor((j-1)/2)+1. Choose N above all wall supports in this finite prefix.
Delete negative-height obstacles and replace the pre-eaten half-plane by the
finite column (-1,0), ..., (-1,N-1). Keep all recorded eaten squares in the
nonnegative quadrant. The remaining set has at most N+t members. For every
transition strictly before the incoming wall, the two tested cells have first
coordinate at least -1 and nonnegative height below N. Their membership is
unchanged by truncation. Nice protection preserves the old outside squares
when the obstacle set is frozen. Thus the finite static walk reproduces the
entire prefix through the incoming wall. At the contact vertex it next turns
east along the bottom of square (x,0), reaching (x+1,0).

On a finite obstacle set, the wall successor is injective on boundary walls:
the explicit predecessor is a left inverse. Consequently its orbit is a
cycle. This octagonal corner convention keeps every occupied support in one
side-connected component; at a concave turn, the intermediate occupied square
supplies the two-edge connection. Apply the imported, proved Claim 4.2 to this
component. A simple cycle has no more walls than its component's perimeter,
so some positive return length L satisfies L <= 2(N+t)+2. This argument does
not assume that the entire obstacle set is connected.

The initial cycle must contain the north-facing top wall of the retained
column. Indeed, following that wall turns onto the column's west side, walks
down it, and turns along the bottom wall back to the initial wall; injectivity
on the finite cycle forces the top wall to lie on the initial orbit. Its start
vertex is (0,N), and it cannot occur in the prefix, whose vertices are all
below N. Immediately after painting that top wall, the vertex is (-1,N).

The potential y-x increases by at most one on any unit directed wall. Between
(x+1,0) and (0,N), at least N+x+1 walls are therefore needed. The potential x-y
likewise shows that at least N+1 walls are needed from (-1,N) to the origin.
Including the east wall after first contact and the west wall at the column
top gives L >= j+2N+x+4 >= j+2N+5. Since j >= 2t-1, this contradicts the upper
bound. Strong induction rules out every first contact. A return to the initial
wall would have start vertex (0,0), so no positive-index return is possible.

All truncation, cycle, component, column, and potential estimates are proved
in the submitted file. The sole imported theorem is connectedSquares_perimeter
(Claim 4.2); it is actually used in the cycle upper bound. The original
wallTrace_never_returns statement and original game definitions are unchanged.
