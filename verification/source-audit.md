# Source-to-model audit — 2026-10-18

Source: Mathe, *The Angel of power 2 wins*, author manuscript, 9 pages.
DOI and exact downloaded-file SHA-256 are recorded in `papers/source.json`.
PDF pages 2 and 8 were rendered and visually checked, in addition to text reading.

| Source | Encoding | Boundary/convention |
|---|---|---|
| Section 1 and notation, pp. 1–2 | `Point`, `Jump`, `InBox` | Infinite integer lattice; Chebyshev distance via four integer inequalities |
| Definition 2.5, p. 2 | `Journey` | Nonempty; starts at origin; consecutive jumps ≤ p; zero-length moves permitted |
| Devil strategy discussion, p. 2 | `DevilStrategy` | Total extension of a journey-dependent optional-square function; may pass |
| Devil-first convention, p. 2 | `step`, `play` | Angel observes the current Devil action before choosing its destination |
| Landing rule, p. 1 | `Survives` | Checks every round against all eaten squares including the current action |
| Definition 2.2 and equation (2), pp. 2–3 | `Nice` | Protect origin and p-neighbourhoods of all positions before the current one |
| Definition 2.3, p. 2 | `Escapes`, `NiceCanConfine` | Escape means unbounded range, not eventual departure from each box; confinement covers every safe finite prefix |
| Theorem 2.7, p. 3 + determinacy observation, p. 1 | `nice_devil_reduction` | Uses absence of an Angel winning strategy; determinacy must therefore be proved within this milestone, not silently assumed |
| Theorem 4.5, p. 8 | `power_two_beats_nice_devil` | One strategy survives and escapes against all Nice Devils |
| Theorem 4.6, p. 8 | `power_two_wins` | One strategy survives against all unrestricted Devils |

The current model follows the paper's convention allowing the Devil to name the
occupied square; the Angel loses on an eaten landing, not at the Devil's selection
itself. Repeated Devil selections are also allowed. All strategies are total on
off-path inputs, and play continues mathematically after failure. Survival filters
these continuations. Quantifier order is `exists Angel, forall Devil`.

The independent auditor received only the Lean declarations and the auditor
instructions, not this source audit or the intended prose. Its final read-backs
use the finite-prefix confinement definition. The captain compared those
read-backs with the source before uploading the proposal.

## Proven increment versus open obligations

The initial increment had nine elementary foundations. The current closed library
has 52 checked lemmas. Claim 2.6 (preservation of Allowed) and Theorem 2.4
(transfer of confinement) are locally proved without open imports. `wall_budget_contradiction`
proves only the integer-arithmetic incompatibility of the four estimates used
at the end of Proposition 4.3. It does not establish the geometric estimates.
`nice_escape_and_reduction_imply_win` assumes both milestones, so it does not
constitute an unconditional proof of the main theorem.

Remaining work includes strategic determinacy/compactness, connected-square perimeter estimates, and a precise wall-following
strategy with its escape proof. The square-boundary and intermediate geometric
claims are not yet encoded as standalone proposal items. The current two
milestones are large, faithful targets that require that additional work.

## Platform lookup

Checked API v0.12.7 on 2026-10-18. Quoted searches for `Nice Devil` and
`The Angel of power 2` returned no results; quoted `angel` returned four unrelated
risk-control entries. Exact new declaration-name checks found no duplicates.
This is a bounded keyword check, not an exhaustive proof that no equivalent
formalization exists anywhere on the platform. Raw search responses remain local.

## Section 2 proof audit

`reducedJourney_prefix` locates each nonempty reduced prefix in an original
prefix. Its witness need not be the earliest occurrence of that endpoint; the
recursive bound suffices. For the final reduced landing, all such witnesses
are at or before its earliest predecessor. Equation (2) cannot suppress that
landing square there, since all tested positions are strictly earlier than the
earliest predecessor. Earlier reduced landings are handled recursively. This
proves Claim 2.6 without needing a separate pairwise-distinctness lemma.

`Allowed` forbids every earlier Devil selection at each landing, not only the
immediately preceding selection. Its prefix closure and its correspondence
with safe strategy play are proved. A scripted Angel realizes any given finite
journey. Together these establish `confinement_iff_allowed`, closing the
interface between the paper's history presentation and the mission's
strategy-quantified finite-prefix definition.

`confinement_to_nice` proves Theorem 2.4 with the original radius, including
zero-power/zero-radius cases. See `section2-readbacks.json` for the independent
readback. The separate `uniform_confinement` target retains both the absence
of an Angel winning strategy and the uniform choice of one radius and one
Devil before all Angels and times. It remains unproved; determinacy is not
introduced as an extra hypothesis or axiom.
