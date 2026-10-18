For every nonnegative integer power, reducing a finite legal journey gives a
finite legal journey. This is the structural assertion immediately following
equation (1) in Section 2 of Mathe's paper. It does not yet establish Claim 2.6,
which also concerns squares eaten under two different Devil strategies.

The proof is by well-founded induction on the length of the original history.
A journey ending at the origin reduces to the singleton origin journey.
Otherwise, the final legal step guarantees that the list preceding the endpoint
contains a reachable predecessor, so the malformed-input fallback cannot occur.
Take the prefix through the earliest such predecessor. It is a nonempty shorter
journey, and hence its reduction is a journey by induction. Reduction preserves
the endpoint of this prefix. The chosen predecessor can reach the original final
point, so appending that point gives a legal journey again.

The supporting list lemmas justify taking prefixes, removing the last point,
and appending a legal final step. The earliest-index function supplies both a
reachable selected point and the exclusion of earlier reachable points. No
winning-strategy hypothesis is used in this proof, and no open paper milestone
is imported.
