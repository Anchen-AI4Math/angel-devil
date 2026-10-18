import Definitions.Def_AngelDevil_NiceReduction
import Solutions.ReducedJourney

namespace AngelDevil

theorem niceReduction_eq_some_iff (p : Nat) (D : DevilStrategy)
    (h : List Point) (z : Point) :
    niceReduction p D h = some z ↔
      D (reducedJourney p h) = some z ∧ NiceEligible p h z := by
  unfold niceReduction
  cases he : D (reducedJourney p h) with
  | none => simp
  | some w =>
    by_cases hw : NiceEligible p h w
    · simp [hw]
      intro hh
      subst z
      exact hw
    · simp [hw]
      intro hh
      subst z
      exact hw

theorem niceReduction_is_nice (p : Nat) (D : DevilStrategy) :
    Nice p (niceReduction p D) := by
  intro h _ z hz
  exact ((niceReduction_eq_some_iff p D h z).mp hz).2

theorem allowed_take (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p D h) (k : Nat) (hk : 0 < k) : Allowed p D (h.take k) := by
  refine ⟨journey_take p h ha.1 k hk, ?_⟩
  intro i j z hij hz
  have hjk : j < k := by
    apply Classical.byContradiction
    intro hn
    simp [List.getElem?_take, hn] at hz
  rw [List.getElem?_take, if_pos hjk] at hz
  simpa only [List.take_take, Nat.min_eq_left (by omega : i+1 ≤ k)]
    using ha.2 i j z hij hz

theorem visited_take (A : AngelStrategy) (D : DevilStrategy) (n k : Nat)
    (hk : k ≤ n) : (play A D n).visited.take (k+1) = (play A D k).visited := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      subst k
      rfl
  | succ n ih =>
      by_cases hkn : k ≤ n
      · change List.take (k+1) ((play A D n).visited ++ [_]) = _
        rw [List.take_append_of_le_length (by rw [(play_lengths A D n).1]; omega)]
        exact ih hkn
      · have : k = n+1 := by omega
        subst k
        rw [← (play_lengths A D (n+1)).1, List.take_length]

theorem past_devil_move_mem (A : AngelStrategy) (D : DevilStrategy) (n i : Nat)
    (hi : i < n) : D (play A D i).visited ∈ (play A D n).burned := by
  induction n with
  | zero => omega
  | succ n ih =>
      change D (play A D i).visited ∈ (play A D n).burned ++ [_]
      by_cases hin : i < n
      · exact List.mem_append_left _ (ih hin)
      · have : i = n := by omega
        subst i
        exact List.mem_append_right _ (by simp)

/- Connect the finite-history formulation to every safe prefix of the original
strategy semantics; no assumption of infinite survival is made. -/
theorem safe_prefix_allowed (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (safe : ∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) :
    Allowed p D (play A D n).visited := by
  refine ⟨safe_prefix_journey p A D n (fun m hm => (safe m hm).1), ?_⟩
  intro i j z hij hz he
  have hjn : j ≤ n := by
    have hl := (List.getElem?_eq_some_iff.mp hz).1
    rw [(play_lengths A D n).1] at hl
    omega
  rw [visited_get A D n j hjn] at hz
  cases hz
  rw [visited_take A D n i (by omega)] at he
  have heaten := past_devil_move_mem A D j i hij
  rw [he] at heaten
  have hj : j-1+1 = j := by omega
  have hs := (safe (j-1) (by omega)).2
  rw [hj] at hs
  exact hs heaten

end AngelDevil
