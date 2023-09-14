import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p


/- 3a (page 21) -/
theorem problem_3a {p q r : Prop} (h1: p ∧ q → r) : p → (q → r) := by
  intro hp
  intro hq
  have hpq: p ∧ q := by apply And.intro hp hq
  apply h1 hpq

/- 3b (page 23) -/
theorem problem_3b {p q r : Prop} (h1: p → ( q → r )) : ( p → q ) → ( p → r ) := by
  intro hpq
  intro hp 
  have hq : q := by apply hpq hp
  apply h1 hp hq


/- 3c (page 24)-/
theorem problem_3c {p q r : Prop} (h1: (p∧¬q)→ r) (h2: ¬r) (h3: p) : q := by
  have hnnq: ¬¬q := by 
    intro hnq
    have hpnq : p ∧ ¬q := by apply And.intro h3 hnq
    have hr : r := by apply h1 hpnq
    contradiction
  apply notnotE hnnq

---------------------

/- 4a (1.3.1)-/
example {a b : ℤ } (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := 
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring
  
/- 4b (1.3.2)-/
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 := 
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

/- 4c (1.3.3)-/
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * (b + 2 - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw [h1, h2]
    _ = 9 := by ring