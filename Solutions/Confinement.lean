import Solutions.NiceReduction

namespace AngelDevil

def scriptedAngel (h : List Point) : AngelStrategy := fun visited _ =>
  h[visited.length]?.getD origin

theorem scripted_visited (p : Nat) (h : List Point) (hj : Journey p h)
    (D : DevilStrategy) (n : Nat) (hn : n < h.length) :
    (play (scriptedAngel h) D n).visited = h.take (n+1) := by
  induction n with
  | zero =>
      change [origin] = h.take 1
      simp [List.take_one, hj.1]
  | succ n ih =>
      change (play (scriptedAngel h) D n).visited ++
        [h[(play (scriptedAngel h) D n).visited.length]?.getD origin] = _
      rw [(play_lengths (scriptedAngel h) D n).1, ih (by omega)]
      rw [List.getElem?_eq_getElem hn]
      simp only [Option.getD_some]
      exact (List.take_succ_eq_append_getElem hn).symm

theorem scripted_current (p : Nat) (h : List Point) (hj : Journey p h)
    (D : DevilStrategy) (n : Nat) (hn : n < h.length) :
    current (play (scriptedAngel h) D n) = h[n] := by
  unfold current
  rw [scripted_visited p h hj D n hn, take_last h n hn]

theorem burned_mem_iff (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (z : Option Point) :
    z ∈ (play A D n).burned ↔ ∃ i, i < n ∧ D (play A D i).visited = z := by
  induction n with
  | zero => simp [play, initial]
  | succ n ih =>
      change z ∈ (play A D n).burned ++ [D (play A D n).visited] ↔ _
      rw [List.mem_append, List.mem_singleton, ih]
      constructor
      · intro hh
        rcases hh with ⟨i, hi, he⟩ | he
        · exact ⟨i, by omega, he⟩
        · exact ⟨n, by omega, he.symm⟩
      · rintro ⟨i, hi, he⟩
        by_cases hin : i < n
        · exact Or.inl ⟨i, hin, he⟩
        · have : i = n := by omega
          subst i
          exact Or.inr he.symm

theorem allowed_scripted_safe (p : Nat) (D : DevilStrategy) (h : List Point)
    (ha : Allowed p D h) (m : Nat) (hm : m+1 < h.length) :
    Jump p (current (play (scriptedAngel h) D m))
      (current (play (scriptedAngel h) D (m+1))) ∧
    some (current (play (scriptedAngel h) D (m+1))) ∉
      (play (scriptedAngel h) D (m+1)).burned := by
  rw [scripted_current p h ha.1 D m (by omega), scripted_current p h ha.1 D (m+1) hm]
  constructor
  · exact ha.1.2 m _ _ (List.getElem?_eq_getElem (by omega))
      (List.getElem?_eq_getElem hm)
  · intro hz
    obtain ⟨i, hi, he⟩ := (burned_mem_iff (scriptedAngel h) D (m+1) _).mp hz
    rw [scripted_visited p h ha.1 D i (by omega)] at he
    exact ha.2 i (m+1) _ hi (List.getElem?_eq_getElem hm) he

/- Finite-history confinement is equivalent to confinement of all safe plays. -/
theorem confinement_iff_allowed (p N : Nat) (D : DevilStrategy) :
    (∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) ↔
    (∀ h, Allowed p D h → InBox N (h.getLastD origin)) := by
  constructor
  · intro hc h ha
    have hne : h ≠ [] := by
      intro he
      have hh := ha.1.1
      simp [he] at hh
    have hl := List.length_pos_iff.mpr hne
    have hs := hc (scriptedAngel h) (h.length-1)
      (fun m hm => allowed_scripted_safe p D h ha m (by omega))
    unfold current at hs
    rw [scripted_visited p h ha.1 D (h.length-1) (by omega),
      show h.length-1+1 = h.length by omega, List.take_length] at hs
    exact hs
  · intro hc A n hs
    exact hc _ (safe_prefix_allowed p A D n hs)

/- Theorem 2.4, with the same finite-prefix confinement semantics as the mission.
Positivity is unnecessary for this reduction alone. -/
theorem confinement_to_nice (p N : Nat) (D : DevilStrategy)
    (hc : ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) : NiceCanConfine p N := by
  refine ⟨niceReduction p D, niceReduction_is_nice p D, ?_⟩
  apply (confinement_iff_allowed p N (niceReduction p D)).mpr
  intro h ha
  have hne : h ≠ [] := by
    intro he
    have hh := ha.1.1
    simp [he] at hh
  have hh := (confinement_iff_allowed p N D).mp hc _ (reducedJourney_allowed p D h ha)
  rw [reducedJourney_endpoint p h hne] at hh
  exact hh

end AngelDevil
