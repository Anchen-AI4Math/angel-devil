import Mathlib.Combinatorics.Compactness
import Solutions.FiniteHorizon

namespace AngelDevil

/- The limit-strategy step in the proof of Claim 2.1. Rado selection is applied
to finite observations, not to an unjustified finite set of Devil choices. -/
theorem finite_survival_compactness (p : Nat)
    (hf : ∀ n, FiniteAngelWins p n) : AngelWins p := by
  classical
  let f : Nat → Observation → BoundedMove p :=
    fun n => Classical.choose (finiteAngelWins_bounded p n (hf n))
  have hsafe : ∀ n D, SafeFor p (boundedAngel p (f n)) D n := by
    intro n
    exact Classical.choose_spec (finiteAngelWins_bounded p n (hf n))
  let horizon : Finset Observation → Nat := fun s => s.sup (fun o => o.1.length)
  let g : Finset Observation → Observation → BoundedMove p := fun s => f (horizon s)
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  refine ⟨boundedAngel p χ, ?_⟩
  intro D n
  let A := boundedAngel p χ
  let obs : Nat → Observation := fun m =>
    ((play A D m).visited, (play A D m).burned ++ [D (play A D m).visited])
  let s : Finset Observation := (Finset.range (n+1)).image obs
  obtain ⟨t, hst, ht⟩ := hχ s
  have hmem : ∀ m, m ≤ n → obs m ∈ s := by
    intro m hm
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩
  have hn : n < horizon t := by
    have hbound : (obs n).1.length ≤ horizon t :=
      Finset.le_sup (f := fun o : Observation => o.1.length) (hst (hmem n (by omega)))
    have hlen : (obs n).1.length = n+1 := (play_lengths A D n).1
    omega
  have hagree : ∀ m, m ≤ n →
      boundedAngel p (g t) (play A D m).visited
        ((play A D m).burned ++ [D (play A D m).visited]) =
      A (play A D m).visited
        ((play A D m).burned ++ [D (play A D m).visited]) := by
    intro m hm
    have he := ht (obs m) (hmem m hm)
    change decodeMove p _ (g t (obs m)) = decodeMove p _ (χ (obs m))
    rw [he]
  have heq : ∀ k, k ≤ n+1 → play (boundedAngel p (g t)) D k = play A D k := by
    intro k hk
    exact play_eq_of_agreement A (boundedAngel p (g t)) D k
      (fun m hm => hagree m (by omega))
  have hs := hsafe (horizon t) D n hn
  change Jump p (current (play (boundedAngel p (g t)) D n))
      (current (play (boundedAngel p (g t)) D (n+1))) ∧
    some (current (play (boundedAngel p (g t)) D (n+1))) ∉
      (play (boundedAngel p (g t)) D (n+1)).burned at hs
  rw [heq n (by omega), heq (n+1) (by omega)] at hs
  exact hs

theorem no_win_has_finite_obstruction (p : Nat) (h : ¬ AngelWins p) :
    ∃ n, ¬ FiniteAngelWins p n := by
  classical
  by_contra hn
  apply h
  apply finite_survival_compactness p
  simpa using hn

end AngelDevil
