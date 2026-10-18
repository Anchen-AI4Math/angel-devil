Normalize Angel strategies to the finite set of legal displacements, without
changing any safe finite play. Apply Mathlib's Rado selection lemma to finite
sets of strategy observations. For each such set choose a strategy safe for at
least the largest visited-history length in that set.

For any proposed finite play of the selected limiting strategy, its observations
form a finite set. Rado selection supplies a finite-horizon strategy agreeing
on all those observations, with a horizon long enough to cover that play.
Induction on rounds proves the plays identical. Thus every round is safe.
The Devil's possible selections are not assumed finite.
