import Definitions.Def_AngelDevil_Game

namespace AngelDevil

instance jumpDecidable (p : Nat) (u v : Point) : Decidable (Jump p u v) := by
  unfold Jump
  infer_instance

def firstReachable (p : Nat) (h : List Point) (z : Point) : Nat :=
  h.findIdx (fun v => decide (Jump p v z))

/- Section 2, equation (1). The recursive predecessor is the earliest point in
the ORIGINAL prefix that can reach the endpoint, not an arbitrary loop erasure.
The singleton fallback only specifies a total function on malformed journeys.
-/
def reducedJourney (p : Nat) (h : List Point) : List Point :=
  if _hnil : h = [] then [] else
  let z := h.getLastD origin
  if z = origin then [origin] else
  let prior := h.dropLast
  let i := firstReachable p prior z
  if i < prior.length then
    reducedJourney p (prior.take (i+1)) ++ [z]
  else [z]
termination_by h.length
decreasing_by
  have hpos : 0 < h.length := List.length_pos_iff.mpr _hnil
  simp only [List.length_take, List.length_dropLast]
  omega

end AngelDevil
