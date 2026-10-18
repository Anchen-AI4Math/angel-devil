import Definitions.Def_AngelDevil_Game

namespace AngelDevil

def SafeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat) : Prop :=
  ∀ m, m < n →
    Jump p (current (play A D m)) (current (play A D (m+1))) ∧
    some (current (play A D (m+1))) ∉ (play A D (m+1)).burned

def FiniteAngelWins (p n : Nat) : Prop := ∃ A, ∀ D, SafeFor p A D n

abbrev Observation := List Point × List (Option Point)
abbrev BoundedMove (p : Nat) := Fin (2*p+1) × Fin (2*p+1)

def decodeMove (p : Nat) (h : List Point) (d : BoundedMove p) : Point :=
  ((h.getLastD origin).1 + (d.1.val : Int) - (p : Int),
   (h.getLastD origin).2 + (d.2.val : Int) - (p : Int))

def boundedAngel (p : Nat) (f : Observation → BoundedMove p) : AngelStrategy :=
  fun h b => decodeMove p h (f (h, b))

/- Invalid off-path choices are replaced by staying put. Legal choices are
encoded exactly, so this changes no safe finite play. -/
noncomputable def encodeAngel (p : Nat) (A : AngelStrategy) :
    Observation → BoundedMove p := by
  classical
  intro o
  let v := A o.1 o.2
  let u := o.1.getLastD origin
  exact if hv : Jump p u v then
    (⟨(v.1-u.1+(p : Int)).toNat, by unfold Jump at hv; omega⟩,
     ⟨(v.2-u.2+(p : Int)).toNat, by unfold Jump at hv; omega⟩)
  else (⟨p, by omega⟩, ⟨p, by omega⟩)

end AngelDevil
