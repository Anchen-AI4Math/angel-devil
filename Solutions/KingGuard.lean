import Solutions.Foundation
import Definitions.Def_AngelDevil_KingGuard
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace AngelDevil





/-- Before a Devil move, a rank-n guard needs at most n further king moves
before it can maintain a complete triple on the defended line. -/


theorem kingOffset_bounds (i : Fin 3) : -1 ≤ kingOffset i ∧ kingOffset i ≤ 1 := by
  unfold kingOffset
  have := i.isLt
  omega

theorem kingOffset_exhaustive (z : Int) (h : -1 ≤ z ∧ z ≤ 1) :
    ∃ i : Fin 3, kingOffset i = z := by
  refine ⟨⟨(z+1).toNat, by omega⟩, ?_⟩
  change ((z+1).toNat : Int) - 1 = z
  omega

theorem guardSquare_bounds (x : Int) (i : Fin 11) :
    x-5 ≤ guardSquare x i ∧ guardSquare x i ≤ x+5 := by
  unfold guardSquare
  have := i.isLt
  omega

theorem kingGuard_mono (n : Nat) (x : Int) {B C : Finset Int}
    (hBC : B ⊆ C) (h : KingGuard n x B) : KingGuard n x C := by
  induction n generalizing x B C with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => Finset.insert_subset_insert _ hBC (hi j)⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := h
    exact ⟨i, fun j => ih _ (Finset.insert_subset_insert _ hBC) (hi j)⟩

theorem triple_has_guard {x : Int} {B : Finset Int}
    (h : ∀ i : Fin 3, x + kingOffset i ∈ B) (j : Fin 3) :
    KingGuard 0 (x + kingOffset j) B := by
  let a : Fin 11 := ⟨(5 + kingOffset j).toNat, by
    have := kingOffset_bounds j
    omega⟩
  refine ⟨a, ?_⟩
  intro k
  have hj := kingOffset_bounds j
  have hk := kingOffset_bounds k
  by_cases hs : -1 ≤ kingOffset j + kingOffset k ∧ kingOffset j + kingOffset k ≤ 1
  · obtain ⟨i, hi⟩ := kingOffset_exhaustive _ hs
    apply Finset.mem_insert_of_mem
    convert h i using 1 <;> omega
  · apply Finset.mem_insert.mpr
    left
    dsimp [guardSquare, a]
    omega

theorem kingGuard_translate (n : Nat) (x t : Int) {B C : Finset Int}
    (hBC : ∀ b ∈ B, b+t ∈ C) (h : KingGuard n x B) :
    KingGuard n (x+t) C := by
  induction n generalizing x B C with
  | zero =>
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    intro j
    have hh := hi j
    simp only [Finset.mem_insert] at hh ⊢
    rcases hh with hh | hh
    · left
      dsimp [guardSquare] at *
      omega
    · right
      convert hBC _ hh using 1 <;> omega
  | succ n ih =>
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    intro j
    have hh := ih (x+kingOffset j) (B := insert (guardSquare x i) B)
      (C := insert (guardSquare (x+t) i) C) (by
        intro b hb
        simp only [Finset.mem_insert] at hb ⊢
        rcases hb with hb | hb
        · left
          dsimp [guardSquare] at *
          omega
        · exact Or.inr (hBC b hb)) (hi j)
    convert hh using 1 <;> omega

theorem kingGuard_step (n : Nat) (x : Int) (B : Finset Int)
    (h : KingGuard n x B) :
    ∃ z, x-5 ≤ z ∧ z ≤ x+5 ∧
      (n = 0 → ∀ j : Fin 3, x + kingOffset j ∈ insert z B) ∧
      ∀ j : Fin 3, KingGuard (n-1) (x+kingOffset j) (insert z B) := by
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := h
    exact ⟨guardSquare x i, (guardSquare_bounds x i).1,
      (guardSquare_bounds x i).2, fun _ => hi, triple_has_guard hi⟩
  | succ n =>
    obtain ⟨i, hi⟩ := h
    exact ⟨guardSquare x i, (guardSquare_bounds x i).1,
      (guardSquare_bounds x i).2, by omega, hi⟩

end AngelDevil
