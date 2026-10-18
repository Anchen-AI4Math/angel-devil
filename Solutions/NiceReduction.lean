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

theorem endpoint_eligible_at_earlier_prefix (p : Nat) (h : List Point)
    (hz : h.getLastD origin ≠ origin) (k : Nat)
    (hi : firstReachable p h.dropLast (h.getLastD origin) < h.dropLast.length)
    (hk : k ≤ firstReachable p h.dropLast (h.getLastD origin)) :
    NiceEligible p (h.take (k+1)) (h.getLastD origin) := by
  refine ⟨hz, ?_⟩
  intro v hv
  have hlen : firstReachable p h.dropLast (h.getLastD origin) < h.length-1 := by
    simpa only [List.length_dropLast] using hi
  rw [List.dropLast_take (by omega : k+1 < h.length)] at hv
  simp only [Nat.add_sub_cancel] at hv
  apply firstReachable_excludes_earlier p h.dropLast (h.getLastD origin) v
  rw [take_dropLast_of_le h _ (by omega)]
  exact (List.take_sublist_take_left hk).subset hv

/- Mathe Claim 2.6: the transformed Devil preserves legality on reduction. -/
theorem reducedJourney_allowed (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p (niceReduction p D) h) : Allowed p D (reducedJourney p h) := by
  induction h using reducedJourney.induct p with
  | case1 => simp [Allowed, Journey] at ha
  | case2 h hne z hz =>
      refine ⟨reducedJourney_is_journey p h ha.1, ?_⟩
      rw [reducedJourney_return p h hne hz]
      intro s t v hst hv
      have ht := (List.getElem?_eq_some_iff.mp hv).1
      simp only [List.length_singleton] at ht
      omega
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      let a := firstReachable p h.dropLast (h.getLastD origin)
      let q := h.dropLast.take (a+1)
      have hlen : a < h.length-1 := by
        simpa only [List.length_dropLast] using hi
      have hq : q = h.take (a+1) := take_dropLast_of_le h _ (by omega)
      have haq : Allowed p (niceReduction p D) q := by
        rw [hq]
        exact allowed_take p _ h ha (a+1) (by omega)
      have hred : Allowed p D (reducedJourney p q) := ih haq
      have hr : reducedJourney p h = reducedJourney p q ++ [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi, q, a]
      refine ⟨reducedJourney_is_journey p h ha.1, ?_⟩
      rw [hr]
      intro s t v hst hv he
      have ht := (List.getElem?_eq_some_iff.mp hv).1
      simp only [List.length_append, List.length_singleton] at ht
      by_cases ht' : t < (reducedJourney p q).length
      · rw [List.getElem?_append_left ht'] at hv
        rw [List.take_append_of_le_length (by omega)] at he
        exact hred.2 s t v hst hv he
      · have hte : t = (reducedJourney p q).length := by omega
        rw [List.getElem?_append_right (by omega), hte] at hv
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
        subst v
        obtain ⟨k, hk, hprefix⟩ := reducedJourney_prefix p q s (by omega)
        have hkbound : k ≤ a := by
          have : q.length ≤ a+1 := by
            dsimp only [q]
            rw [List.length_take]
            exact Nat.min_le_left _ _
          omega
        have hprefix' : reducedJourney p (h.take (k+1)) =
            (reducedJourney p q).take (s+1) := by
          rw [hq, List.take_take, Nat.min_eq_left (by omega : k+1 ≤ a+1)] at hprefix
          simpa only [hq] using hprefix
        rw [List.take_append_of_le_length (by omega), ← hprefix'] at he
        have hn : niceReduction p D (h.take (k+1)) = some (h.getLastD origin) := by
          apply (niceReduction_eq_some_iff p D _ _).mpr
          exact ⟨he, endpoint_eligible_at_earlier_prefix p h hz k hi hkbound⟩
        exact ha.2 k (h.length-1) (h.getLastD origin) (by omega)
          (last_lookup h hne) hn
  | case4 h hne z hz prior i hbad =>
      exact False.elim (hbad (journey_last_has_predecessor p h ha.1 hz))

end AngelDevil
