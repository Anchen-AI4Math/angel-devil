import Definitions.Def_AngelDevil_ReducedJourney
import Solutions.Histories

namespace AngelDevil

theorem reducedJourney_nil (p : Nat) : reducedJourney p [] = [] := by
  rw [reducedJourney]
  simp

theorem reducedJourney_return (p : Nat) (h : List Point) (hne : h ≠ [])
    (hend : h.getLastD origin = origin) : reducedJourney p h = [origin] := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte, hend, ↓reduceIte]

theorem reducedJourney_nonempty (p : Nat) (h : List Point) (hne : h ≠ []) :
    reducedJourney p h ≠ [] := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte]
  split
  · simp
  · split <;> simp

theorem reducedJourney_endpoint (p : Nat) (h : List Point) (hne : h ≠ []) :
    (reducedJourney p h).getLastD origin = h.getLastD origin := by
  rw [reducedJourney]
  simp only [hne, ↓reduceDIte]
  split
  · rename_i he
    simpa using he.symm
  · split <;> simp

theorem firstReachable_jump (p : Nat) (h : List Point) (z : Point)
    (hi : firstReachable p h z < h.length) :
    Jump p h[firstReachable p h z] z := by
  exact of_decide_eq_true (List.findIdx_getElem (w := hi))

theorem firstReachable_minimal (p : Nat) (h : List Point) (z : Point) (j : Nat)
    (hj : j < firstReachable p h z) :
    ¬ Jump p (h[j]'(Nat.lt_of_lt_of_le hj List.findIdx_le_length)) z := by
  have hfalse := List.not_of_lt_findIdx hj
  simpa using hfalse

theorem last_lookup (h : List Point) (hne : h ≠ []) :
    h[h.length-1]? = some (h.getLastD origin) := by
  rw [← List.getLast?_eq_getElem?]
  simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
    Option.getD_some]

theorem journey_take (p : Nat) (h : List Point) (hj : Journey p h)
    (k : Nat) (hk : 0 < k) : Journey p (h.take k) := by
  constructor
  · simpa [List.head?_take, Nat.ne_of_gt hk] using hj.1
  · intro i u v hu hv
    have hi : i+1 < k := by
      apply Classical.byContradiction
      intro hn
      simp [List.getElem?_take, hn] at hv
    rw [List.getElem?_take, if_pos (by omega)] at hu
    rw [List.getElem?_take, if_pos hi] at hv
    exact hj.2 i u v hu hv

theorem journey_dropLast (p : Nat) (h : List Point) (hj : Journey p h)
    (hl : 1 < h.length) : Journey p h.dropLast := by
  constructor
  · simpa [List.head?_dropLast, hl] using hj.1
  · intro i u v hu hv
    have hi : i+1 < h.length-1 := by
      apply Classical.byContradiction
      intro hn
      simp [hn] at hv
    rw [List.getElem?_dropLast, if_pos (by omega)] at hu
    rw [List.getElem?_dropLast, if_pos hi] at hv
    exact hj.2 i u v hu hv

theorem journey_append (p : Nat) (h : List Point) (hj : Journey p h) (z : Point)
    (hjump : Jump p (h.getLastD origin) z) : Journey p (h ++ [z]) := by
  have hne : h ≠ [] := by intro e; have hh := hj.1; rw [e] at hh; contradiction
  have hpos := List.length_pos_iff.mpr hne
  constructor
  · simp [List.head?_append, hj.1]
  · intro i u v hu hv
    have hil : i+1 < (h ++ [z]).length := (List.getElem?_eq_some_iff.mp hv).1
    simp only [List.length_append, List.length_singleton] at hil
    by_cases hin : i+1 < h.length
    · rw [List.getElem?_append_left (by omega)] at hu
      rw [List.getElem?_append_left hin] at hv
      exact hj.2 i u v hu hv
    · have he : i+1 = h.length := by omega
      have hei : i = h.length-1 := by omega
      rw [List.getElem?_append_left (by omega), hei, last_lookup h hne] at hu
      rw [List.getElem?_append_right (by omega), he] at hv
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hv
      cases hu
      subst v
      exact hjump

theorem journey_last_has_predecessor (p : Nat) (h : List Point) (hj : Journey p h)
    (hz : h.getLastD origin ≠ origin) :
    firstReachable p h.dropLast (h.getLastD origin) < h.dropLast.length := by
  have hne : h ≠ [] := by intro e; have hh := hj.1; rw [e] at hh; contradiction
  have hpos := List.length_pos_iff.mpr hne
  have hl : 1 < h.length := by
    apply Classical.byContradiction
    intro hn
    have he : h.length = 1 := by omega
    have hlast := last_lookup h hne
    have hfirst := hj.1
    rw [List.head?_eq_getElem?] at hfirst
    simp only [he, Nat.sub_self] at hlast
    rw [hfirst] at hlast
    exact hz (Option.some.inj hlast).symm
  let j := h.length-2
  have hjl : j < h.length := by omega
  have hpred : h[j]? = some h[j] := List.getElem?_eq_getElem hjl
  have hlast : h[j+1]? = some (h.getLastD origin) := by
    have : j+1 = h.length-1 := by omega
    rw [this]; exact last_lookup h hne
  have hstep := hj.2 j h[j] _ hpred hlast
  apply List.findIdx_lt_length_of_exists
  refine ⟨h[j], ?_, by simpa using hstep⟩
  apply List.mem_of_getElem? (i := j)
  rw [List.getElem?_dropLast, if_pos (by omega)]
  exact hpred

theorem take_last (h : List Point) (i : Nat) (hi : i < h.length) :
    (h.take (i+1)).getLastD origin = h[i] := by
  simp [List.getLastD_eq_getLast?, List.getLast?_take,
    List.getElem?_eq_getElem hi]

theorem reducedJourney_is_journey (p : Nat) (h : List Point) (hj : Journey p h) :
    Journey p (reducedJourney p h) := by
  induction h using reducedJourney.induct p with
  | case1 => simp [Journey] at hj
  | case2 h hne z hz =>
      rw [reducedJourney_return p h hne hz]
      constructor
      · rfl
      · intro i u v hu hv
        have := (List.getElem?_eq_some_iff.mp hv).1
        simp at this
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      have hl : 1 < h.length := by
        have : 0 < h.dropLast.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
        simp only [List.length_dropLast] at this
        omega
      have hprior := journey_take p h.dropLast (journey_dropLast p h hj hl)
        (firstReachable p h.dropLast (h.getLastD origin)+1) (by omega)
      have hpriorne : h.dropLast.take (firstReachable p h.dropLast (h.getLastD origin)+1) ≠ [] := by
        intro e
        have hh := hprior.1
        rw [e] at hh
        contradiction
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi]
      apply journey_append p _ (ih hprior)
      rw [reducedJourney_endpoint _ _ hpriorne, take_last _ _ hi]
      exact firstReachable_jump p _ _ hi
  | case4 h hne z hz prior i hbad =>
      exact False.elim (hbad (journey_last_has_predecessor p h hj hz))

/- The reduction deletes vertices without reordering them, even off legal play. -/
theorem reducedJourney_sublist (p : Nat) (h : List Point) :
    (reducedJourney p h).Sublist h := by
  induction h using reducedJourney.induct p with
  | case1 => simp [reducedJourney_nil]
  | case2 h hne z hz =>
      rw [reducedJourney_return p h hne hz]
      apply List.singleton_sublist.mpr
      dsimp only [z] at hz
      have hh := List.mem_of_getElem? (last_lookup h hne)
      simpa only [hz] using hh
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi]
      have hs := (ih.trans (List.take_sublist _ _)).append_right [h.getLastD origin]
      have he : h.dropLast ++ [h.getLastD origin] = h := by
        simpa [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
          using List.dropLast_concat_getLast hne
      rw [he] at hs
      exact hs
  | case4 h hne z hz prior i hbad =>
      dsimp only [z, prior, i] at hz hbad
      rw [reducedJourney]
      simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hbad]
      exact List.singleton_sublist.mpr (List.mem_of_getElem? (last_lookup h hne))

theorem reducedJourney_length_le (p : Nat) (h : List Point) :
    (reducedJourney p h).length ≤ h.length :=
  (reducedJourney_sublist p h).length_le

/- No vertex strictly before the selected predecessor can reach the endpoint.
This is the exclusion needed when the Nice filter could suppress a Devil move. -/
theorem firstReachable_excludes_earlier (p : Nat) (h : List Point) (z v : Point)
    (hv : v ∈ h.take (firstReachable p h z)) : ¬ Jump p v z := by
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hv
  have hh := firstReachable_minimal p h z j (by omega)
  simpa only [he] using hh

theorem take_dropLast_of_le (h : List Point) (k : Nat) (hk : k ≤ h.length-1) :
    h.dropLast.take k = h.take k := by
  rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hk]

/- Every nonempty reduced prefix is itself the reduction of an original prefix.
The witness is an index in the original history, not a reduced-list index. -/
theorem reducedJourney_prefix (p : Nat) (h : List Point) (s : Nat)
    (hs : s < (reducedJourney p h).length) :
    ∃ k, k < h.length ∧
      reducedJourney p (h.take (k+1)) = (reducedJourney p h).take (s+1) := by
  induction h using reducedJourney.induct p generalizing s with
  | case1 => simp [reducedJourney_nil] at hs
  | case2 h hne z hz =>
      have hr := reducedJourney_return p h hne hz
      rw [hr] at hs ⊢
      have : s = 0 := by simpa using hs
      subst s
      have hl := List.length_pos_iff.mpr hne
      refine ⟨h.length-1, by omega, ?_⟩
      rw [show h.length-1+1 = h.length by omega, List.take_length, hr]
      rfl
  | case3 h hne z hz prior i hi ih =>
      dsimp only [z, prior, i] at hz hi ih
      let q := h.dropLast.take (firstReachable p h.dropLast (h.getLastD origin)+1)
      have hr : reducedJourney p h = reducedJourney p q ++ [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hi, q]
      rw [hr] at hs ⊢
      by_cases hs' : s < (reducedJourney p q).length
      · obtain ⟨k, hk, he⟩ := ih s hs'
        simp only [List.length_take] at hk
        have hk' : k+1 ≤ firstReachable p h.dropLast (h.getLastD origin)+1 := by
          omega
        have hlen : firstReachable p h.dropLast (h.getLastD origin) < h.length-1 := by
          simpa only [List.length_dropLast] using hi
        refine ⟨k, by omega, ?_⟩
        rw [List.take_append_of_le_length (by omega)]
        simpa only [List.take_take, Nat.min_eq_left hk',
          take_dropLast_of_le h (k+1) (by omega)] using he
      · have hl := List.length_pos_iff.mpr hne
        have he : s+1 = (reducedJourney p q ++ [h.getLastD origin]).length := by
          simp only [List.length_append, List.length_singleton] at hs ⊢
          omega
        refine ⟨h.length-1, by omega, ?_⟩
        rw [show h.length-1+1 = h.length by omega, List.take_length, hr, he,
          List.take_length]
  | case4 h hne z hz prior i hbad =>
      dsimp only [z, prior, i] at hz hbad
      have hr : reducedJourney p h = [h.getLastD origin] := by
        rw [reducedJourney]
        simp only [hne, ↓reduceDIte, hz, ↓reduceIte, hbad]
      rw [hr] at hs ⊢
      have : s = 0 := by simpa using hs
      subst s
      have hl := List.length_pos_iff.mpr hne
      refine ⟨h.length-1, by omega, ?_⟩
      rw [show h.length-1+1 = h.length by omega, List.take_length, hr]
      rfl

end AngelDevil
