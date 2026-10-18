import Definitions.Def_AngelDevil_FiniteHorizon
import Solutions.Confinement

namespace AngelDevil

theorem safeFor_mono (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n k : Nat) (hk : k ≤ n) (hs : SafeFor p A D n) : SafeFor p A D k :=
  fun m hm => hs m (by omega)

theorem survives_iff_all_safeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) :
    Survives p A D ↔ ∀ n, SafeFor p A D n := by
  constructor
  · intro hs n m _
    exact hs m
  · intro hs m
    exact hs (m+1) m (by omega)

theorem safeFor_inBox (p : Nat) (A : AngelStrategy) (D : DevilStrategy)
    (n : Nat) (hs : SafeFor p A D n) : InBox (n*p) (current (play A D n)) := by
  induction n with
  | zero => simpa only [Nat.zero_mul, current_zero, InBox] using jump_self 0 origin
  | succ n ih =>
      have hh := jump_add (ih (safeFor_mono p A D (n+1) n (by omega) hs))
        (hs n (by omega)).1
      simpa only [Nat.succ_mul, InBox] using hh

/- Once a fixed Devil forces failure by a uniform finite deadline, bounded
speed supplies a positive box for every safe prefix (Claim 2.1's final step). -/
theorem bounded_failure_confines (p T : Nat) (D : DevilStrategy)
    (hD : ∀ A, ¬ SafeFor p A D T) :
    ∀ A n, SafeFor p A D n → InBox (T*p+1) (current (play A D n)) := by
  intro A n hs
  have hn : n < T := by
    apply Classical.byContradiction
    intro h
    exact hD A (safeFor_mono p A D n T (by omega) hs)
  have hbound : n*p ≤ T*p+1 := by
    have := Nat.mul_le_mul_right p (Nat.le_of_lt hn)
    omega
  exact jump_mono hbound (safeFor_inBox p A D n hs)

theorem decodeMove_legal (p : Nat) (h : List Point) (d : BoundedMove p) :
    Jump p (h.getLastD origin) (decodeMove p h d) := by
  have hx := d.1.isLt
  have hy := d.2.isLt
  unfold Jump decodeMove
  dsimp only
  omega

theorem decode_encode_legal (p : Nat) (A : AngelStrategy) (h : List Point)
    (b : List (Option Point)) (hj : Jump p (h.getLastD origin) (A h b)) :
    boundedAngel p (encodeAngel p A) h b = A h b := by
  simp only [boundedAngel, encodeAngel, hj, ↓reduceDIte, decodeMove]
  apply Prod.ext <;> dsimp only
  all_goals unfold Jump at hj; omega

/- Finite play depends only on the strategy inputs actually visited. -/
theorem play_eq_of_agreement (A B : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (h : ∀ m, m < n →
      B (play A D m).visited ((play A D m).burned ++ [D (play A D m).visited]) =
      A (play A D m).visited ((play A D m).burned ++ [D (play A D m).visited])) :
    play B D n = play A D n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step B D (play B D n) = step A D (play A D n)
      rw [ih (fun m hm => h m (by omega))]
      simp only [step, h n (by omega)]

theorem encode_play_eq (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (hs : SafeFor p A D n) :
    play (boundedAngel p (encodeAngel p A)) D n = play A D n := by
  apply play_eq_of_agreement
  intro m hm
  apply decode_encode_legal
  have hj := (hs m hm).1
  rw [current_succ] at hj
  exact hj

theorem encode_safeFor (p : Nat) (A : AngelStrategy) (D : DevilStrategy) (n : Nat)
    (hs : SafeFor p A D n) : SafeFor p (boundedAngel p (encodeAngel p A)) D n := by
  intro m hm
  rw [encode_play_eq p A D m (safeFor_mono p A D n m (by omega) hs),
      encode_play_eq p A D (m+1) (safeFor_mono p A D n (m+1) (by omega) hs)]
  exact hs m hm

theorem finiteAngelWins_bounded (p n : Nat) (h : FiniteAngelWins p n) :
    ∃ f : Observation → BoundedMove p, ∀ D, SafeFor p (boundedAngel p f) D n := by
  obtain ⟨A, hA⟩ := h
  exact ⟨encodeAngel p A, fun D => encode_safeFor p A D n (hA D)⟩

end AngelDevil
