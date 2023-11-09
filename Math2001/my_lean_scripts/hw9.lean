import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

/- 2 points -/
theorem problem4a (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k hk
  . simp [B]
  . simp [B]
    rw [hk]
    ring


def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

/- 3 points -/
theorem problem4b (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k hk
  . simp [S]
    numbers
  . simp [S]
    rw [hk]
    ring

/- 3 points -/
theorem problem4c (n : ℕ) : S n ≤ 2 := by
  simple_induction n with k hk
  . simp [S]
  . have hs: S (k+1) = 2 - 1 / 2^(k+1) := by apply problem4b
    simp [hs]


def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

/- 3 points -/
theorem problem4d (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  simple_induction n with k hk
  ·
    calc factorial 0 ≤ 1 := by simp [factorial]
      _ ≤  (0 + 1) * factorial 0 := by simp [factorial]
      _ ≤  (0 + 1) * 1 := by simp [factorial]
      _ ≤  1 := by numbers
  ·
    have h_extra : k + 1 ≤ k + 1 + 1 := by extra
    calc factorial (k + 1 + 1) = (k + 1 + 1) * factorial (k + 1) := by simp [factorial]
      _ ≤ (k + 1 + 1) * (k + 1)^k := by rel [hk]
      _ ≤ (k + 1 + 1) * (k + 1 + 1)^k := by rel [h_extra]
      _ = (k + 1 + 1)^(k + 1) := by ring


def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6


/- 3 points -/
theorem problem5a (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k IH1 IH2
  . simp
  . simp
  calc
    q (k+2) = 2 * q (k+1) - q k + 6 * k + 6 := by rw [q]
    _ = 2 * q (k+1) - (↑k ^ 3 + 1) + 6 * k + 6 := by rw [IH1]
    _ = 2 * ((↑k + 1)^3 + 1) - (↑k^3 + 1) + 6 * k + 6 := by rw [IH2]
    _ = (↑k + 1 + 1) ^ 3 + 1 := by ring


def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

/- 3 points -/
theorem problem5b : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 7
  intro n hn
  two_step_induction_from_starting_point n, hn with k hk IH1 IH2
  . calc
      r 7 = 140 := by rfl
      _ ≥ 2^7 := by numbers
  . calc
      r 8 = 338 := by rfl
      _ ≥ 2^8 := by numbers
  . calc
      r (k + 2)
        = 2 * r (k + 1) + r k := by simp [r]
      _ ≥ 2 * 2^(k + 1) + 2^k := by rel [IH1, IH2]
      _ = 2^(k + 1 + 1) + 2^k := by ring
      _ ≥ 2^(k + 1 + 1) := by extra

/- 3 points -/
theorem problem5c (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h_even | h_odd := Nat.even_or_odd n
  . obtain ⟨c, hc⟩ := h_even
    rw [hc] at hn
    cancel 2 at hn
    obtain IH := problem5c c hn
    obtain ⟨a, x, hx, hax⟩ := IH
    use a+1, x
    use hx
    calc
      n = 2 * c := by rw [hc]
      _ = 2 * (2^a * x) := by rw [hax]
      _ = 2^(a + 1) * x := by ring
  . use 0, n
    simp
    apply h_odd
