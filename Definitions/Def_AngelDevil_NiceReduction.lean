import Definitions.Def_AngelDevil_ReducedJourney

namespace AngelDevil

/- Equation (2): protect the origin and the neighbourhood of every position
strictly before the current one. The Devil may still eat the current position
when it is not protected by an earlier position. -/
def NiceEligible (p : Nat) (h : List Point) (z : Point) : Prop :=
  z ≠ origin ∧ ∀ v ∈ h.dropLast, ¬ Jump p v z

instance niceEligibleDecidable (p : Nat) (h : List Point) (z : Point) :
    Decidable (NiceEligible p h z) := by
  unfold NiceEligible
  infer_instance

def niceReduction (p : Nat) (D : DevilStrategy) : DevilStrategy := fun h =>
  match D (reducedJourney p h) with
  | none => none
  | some z => if NiceEligible p h z then some z else none

/- An allowed finite journey: the Devil acts on prefix i before landing j,
so all pairs i < j must be checked, not only consecutive moves. -/
def Allowed (p : Nat) (D : DevilStrategy) (h : List Point) : Prop :=
  Journey p h ∧ ∀ (i j : Nat) (z : Point), i < j → h[j]? = some z →
    D (h.take (i+1)) ≠ some z

end AngelDevil
