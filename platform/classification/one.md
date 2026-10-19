We prove that a single Devil strategy defeats every power-one Angel strategy.

First select the 56 sites in the corner preparation list of a radius-100 square (some selections coincide). During these rounds the king remains within distance 56 of its start, so it cannot reach the boundary. All four line guards can then be initialized using the imported five-burn preparation lemma.

The imported guarded-box step supplies a boundary-preserving burn. If that site was already burned, substitute any unburned square in the finite box: the intended obstacle was already present, and additional obstacles preserve the guard conditions. Every subsequent legal reply remains strictly inside the box, while the number of available squares decreases.

Induction on the finite horizon proves that the resulting position is not viable for more rounds than there are remaining box squares. Prepending the preparation list gives a finite obstruction from the original initial state. The finite-game construction reconstructs a state-dependent Devil as a history-only Devil and proves that this one strategy defeats every Angel by the same finite deadline.

Passing and zero-length Angel moves are covered; a king that stays still is still subject to the finite-exhaustion argument. The result formalizes the known Berlekamp king-capture argument as presented in Kutz, Section 1.1, pp. 2-3. No optimal board size or capture deadline is claimed.
