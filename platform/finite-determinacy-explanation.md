Define viability recursively in the number of remaining rounds: every Devil
selection must admit a safe landing in a viable successor state. At viable
states, choice of such a landing gives one Angel strategy safe for the horizon.
At a nonviable state, classical logic gives one Devil selection making every
safe successor nonviable. Induction on elapsed rounds yields failure by the
deadline.

The counterstrategy initially uses the current burned state. A recursive
reconstruction of its own prior selections from the visited history proves it
is representable by the original history-only DevilStrategy. Hence no extra
information is granted to the Devil and no quantifier exchange is assumed.
