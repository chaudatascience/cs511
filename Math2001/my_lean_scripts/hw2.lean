import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel


-- 5C
theorem de_morgan_2 {p q : Prop} : (h: ¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  obtain ⟨h_np, h_nq⟩ := h
  intro h_pq
  cases h_pq with
  | inl hp => apply h_np hp
  | inr hq => apply h_nq hq
  
-- 5D
theorem de_morgan_3 {p q : Prop} (h: ¬p ∨  ¬q) : ¬(p ∧ q) := by
  intros h_pq
  obtain ⟨h_p, h_q⟩ := h_pq
  cases h with 
   | inl h_np => apply h_np h_p
   | inr h_nq => apply h_nq h_q


-- -- -- -- -- -- -- -- -- -- -- -- -- 

-- Problem 6A
example {x y : ℤ} (h1: x + 3 ≥ 2 * y) (h2: 1 ≤ y) : x ≥ -1 := 
  calc
    x = (x + 3) - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ ≥ -1 := by numbers

-- Problem 6B
example {a b : ℚ} (h1: 3 ≤ a) (h2: a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + (a + 2 * b)) / 2:= by ring
    _ ≥  (a + 4) / 2 := by rel [h2]
    _ ≥ (3 + 4) / 2 := by rel [h1]
    _ ≥ 3 := by numbers

-- Problem 6C
example {x : ℤ} (hx : x ≥ 9) : x^3 - 8 * x^2 + 2 * x ≥ 3 :=
  calc
    x^3 - 8 * x^2 + 2 * x
    = x * x^2 - 8 * x^2 + 2 * x := by ring
    _ ≥ 9 * x^2 - 8 * x^2 + 2 * x := by rel [hx]
    _ = x^2 + 2 * x := by ring
    _ ≥ 9^2 + 2 * 9 := by rel [hx]
    _ ≥ 3 := by numbers

  
