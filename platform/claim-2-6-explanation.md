This proves Mathe's Claim 2.6 using the equation (2) transformation.

Induct along the recursive earliest-predecessor construction. Every nonempty
prefix of a reduced journey is the reduction of some original prefix. If the
last vertex is not the origin, every original position strictly before its
earliest predecessor is too far away to protect that last vertex under the
Nice filter. A Devil selection of this last vertex on any reduced prefix would
therefore also be made by the transformed Devil on the corresponding original
prefix, contradicting allowedness. Earlier reduced landings are handled by the
induction hypothesis. Origin-ending histories reduce to a singleton.

The submitted proof imports and uses the published preservation-of-Journey
theorem `09953273-0806-4e9f-a1da-0b10a2292ffb`. The closed local proof also builds
independently without importing any open platform theorem placeholders.
