import Solutions.KingBox

namespace AngelDevil

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000



theorem kingBurned_mem (s : State) (p : Point) : p ∈ kingBurned s ↔ some p ∈ s.burned := by
  simp [kingBurned]

theorem kingBurned_advance (s : State) (z q : Point) :
    kingBurned (advance s (some z) q) = insert z (kingBurned s) := by
  ext p
  simp [kingBurned_mem, advance, eq_comm, or_comm]

theorem king_current_advance (s : State) (d : Option Point) (q : Point) :
    current (advance s d q) = q := by simp [current, advance]

theorem king_box_fresh_step (p : Point) (B : Finset Point) (h : KingBoxReady p B)
    (hex : (kingBoard \ B).Nonempty) :
    ∃ z ∈ kingBoard \ B, ∀ q, Jump 1 p q → q ∉ insert z B → KingBoxReady q (insert z B) := by
  obtain ⟨z,hz,hstep⟩ := king_box_step p B h
  by_cases hb : z ∈ B
  · obtain ⟨w,hw⟩ := hex
    refine ⟨w,hw,?_⟩
    intro q hj hq
    have hqB : q ∉ B := fun hh => hq (Finset.mem_insert_of_mem hh)
    have hh := hstep q hj (by simpa [Finset.insert_eq_of_mem hb] using hqB)
    rw [Finset.insert_eq_of_mem hb] at hh
    exact kingBoxReady_mono q (Finset.subset_insert _ _) hh
  · exact ⟨z,Finset.mem_sdiff.mpr ⟨hz,hb⟩,hstep⟩

theorem king_trap_not_viable (n : Nat) (s : State)
    (hr : KingBoxReady (current s) (kingBurned s))
    (hc : (kingBoard \ kingBurned s).card < n) : ¬ Viable 1 n s := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    intro hv
    by_cases he : (kingBoard \ kingBurned s).Nonempty
    · obtain ⟨z,hz,hstep⟩ := king_box_fresh_step _ _ hr he
      obtain ⟨q,hj,hq,hv'⟩ := hv (some z)
      have hqb : q ∉ insert z (kingBurned s) := by
        rw [← kingBurned_advance s z q, kingBurned_mem]
        exact hq
      have hr' := hstep q hj hqb
      apply ih (advance s (some z) q)
      · simpa [king_current_advance, kingBurned_advance] using hr'
      · rw [kingBurned_advance]
        have hid : kingBoard \ insert z (kingBurned s) =
            (kingBoard \ kingBurned s).erase z := by
          ext v
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [hid, Finset.card_erase_of_mem hz]
        have := Finset.card_pos.mpr he
        omega
      · exact hv'
    · obtain ⟨z,_,hstep⟩ := king_box_step _ _ hr
      obtain ⟨q,hj,hq,_⟩ := hv (some z)
      have hqb : q ∉ insert z (kingBurned s) := by
        rw [← kingBurned_advance s z q, kingBurned_mem]
        exact hq
      have hr' := hstep q hj hqb
      exact he ⟨q, Finset.mem_sdiff.mpr ⟨king_inside_board q hr'.2.1,
        fun hh => hqb (Finset.mem_insert_of_mem hh)⟩⟩

theorem viable_burn_prefix (L : List Point) (T : Nat) (s : State)
    (hv : Viable 1 (L.length+T) s) :
    ∃ s', Viable 1 T s' ∧ kingBurned s' = L.toFinset ∪ kingBurned s ∧
      Jump L.length (current s) (current s') := by
  induction L generalizing s with
  | nil =>
    exact ⟨s, by simpa using hv, by simp, jump_self 0 _⟩
  | cons z L ih =>
    have hh : Viable 1 ((L.length+T)+1) s := by simpa [Nat.add_assoc, Nat.add_comm] using hv
    obtain ⟨q,hj,_,hv'⟩ := hh (some z)
    obtain ⟨s',hs',hb,hjump⟩ := ih (advance s (some z) q) hv'
    refine ⟨s',hs',?_,?_⟩
    · rw [hb, kingBurned_advance]
      ext v
      simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert]
      tauto
    · rw [king_current_advance] at hjump
      simpa [Nat.add_comm] using jump_add hj hjump

theorem power_one_finite_obstruction :
    ¬ Viable 1 (56 + (kingBoard.card+1)) initial := by
  intro hv
  have hv' : Viable 1 (kingCorners.length+(kingBoard.card+1)) initial := by
    simpa [kingCorners_length] using hv
  obtain ⟨s,hs,hb,hj⟩ := viable_burn_prefix kingCorners (kingBoard.card+1) initial hv'
  have hcorners : ∀ z ∈ kingCorners, z ∈ kingBurned s := by
    intro z hz
    rw [hb]
    exact Finset.mem_union_left _ (List.mem_toFinset.mpr hz)
  have hbound : -56 ≤ (current s).1 ∧ (current s).1 ≤ 56 ∧
      -56 ≤ (current s).2 ∧ (current s).2 ≤ 56 := by
    simpa [kingCorners_length, Jump, current, initial, origin] using hj
  have hnorm : ∀ t : Fin 4, kingNormal t (current s) ≤ 56 := by
    intro t
    fin_cases t <;> simp [kingNormal] <;> omega
  have hr : KingBoxReady (current s) (kingBurned s) :=
    ⟨hcorners, fun t => by have := hnorm t; omega,
      fun t => kingLineReady_far t _ _ (by have := hnorm t; omega)⟩
  apply king_trap_not_viable (kingBoard.card+1) s hr _ hs
  have := Finset.card_le_card (Finset.sdiff_subset (s := kingBoard) (t := kingBurned s))
  omega

theorem power_one_bounded_capture : ∃ D : DevilStrategy,
    ∀ A, ¬ SafeFor 1 A D (56 + (kingBoard.card+1)) :=
  ⟨finiteDevil 1 (56 + (kingBoard.card+1)),
    not_viable_forces_failure 1 _ power_one_finite_obstruction⟩

theorem power_one_devil_wins : ∃ D : DevilStrategy, ∀ A, ¬ Survives 1 A D := by
  obtain ⟨D,hD⟩ := power_one_bounded_capture
  exact ⟨D, fun A hA => hD A (fun n _ => hA n)⟩

theorem power_one_not_wins : ¬ AngelWins 1 := by
  obtain ⟨D,hD⟩ := power_one_devil_wins
  rintro ⟨A,hA⟩
  exact hD A (hA D)

end AngelDevil
