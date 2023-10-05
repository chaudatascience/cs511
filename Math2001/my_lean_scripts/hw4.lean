
  import Mathlib.Data.Real.Basic
  import Mathlib.Tactic.IntervalCases
  import Library.Theory.Comparison
  import Library.Theory.Parity
  import Library.Theory.Prime
  import Library.Tactic.ModCases
  import Library.Tactic.Extra
  import Library.Tactic.Numbers
  import Library.Tactic.Addarith
  import Library.Tactic.Cancel
  import Library.Tactic.Use

notation3 (prettyPrint:= false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

---- problem 4
-- 4.a
example {n: ℤ} (hn: Odd n): Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 7 * k + 1 
  calc
    7 * n - 4 = 7 * (2 * k + 1) - 4:= by rw [hk]
    _ = 2 * (7 * k + 1) + 1:= by ring 


-- 4.b
example {x y: ℤ} (hx: Odd x) (hy: Odd y): Odd (x * y + 2 * y) := by
  obtain ⟨a, ha⟩:= hx
  obtain ⟨b, hb⟩:= hy
  use (2 * a * b + a + 3 * b + 1)
  calc
    x * y + 2 * y = (2 * a + 1) * (2 * b + 1) + 2 * (2 * b + 1):= by rw [ha, hb]
    _ = 2 * (2 * a * b + 3 * b + a + 1) + 1:= by ring


-- 4.c
example {n: ℤ} (hn: Even n): Odd (n ^ 2 + 2 * n - 5) := by
  dsimp [Even, Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 2 * k ^ 2 + 2 * k - 3
  calc
    n ^ 2 + 2 * n - 5 = (k + k) ^ 2 + 2 * (k + k) - 5:= by rw [hk] 
    _ = 2 * (2 * k^2 + 2 * k - 3) + 1 := by ring


-- 4.d
example (a b c: ℤ): Even (a - b) ∨ Even (a + c) ∨ Even (b - c):= by
  dsimp [Even, Odd] at *
  obtain hbc | hbc:= Int.even_or_odd (b - c)
  . right
    right
    obtain ⟨x, hbc⟩ := hbc
    use x
    calc
      b - c = 2 * x:= by rw [hbc]
      _ = x + x:= by ring 
  . obtain hac | hac:= Int.even_or_odd (a + c)
    . right
      left
      obtain ⟨x, hac⟩:= hac
      use x
      calc
        a + c = 2 * x:= by rw [hac]
        _ = x + x:= by ring
    . left
      obtain ⟨x, hac⟩:= hac
      obtain ⟨y, hbc⟩:= hbc
      use (x - y - c)
      calc
        a - b = (a + c) - (b - c) - 2 * c:= by ring
        _ = (2 * x + 1) - (b - c) - 2 * c:= by rw [hac]
        _ = (2 * x + 1) - (2 * y + 1) - 2 * c:= by rw [hbc]
        _ = 2 * x - 2 * y - 2 * c:= by ring
        _ = (x - y - c) + (x -y -c):= by ring



---- problem 5
-- 5.a
example {a b: ℝ} (h: ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  obtain h1 | h2 := h ((a + b)/ 2)
  . calc
    b = 2 * ((a + b)/ 2) - a := by ring
    _ ≥ 2 * a - a := by rel [h1]
    _ = a := by ring
  . calc
    a = 2 * ((a + b)/ 2) - b := by ring
    _ ≤ 2 * b - b := by rel [h2]
    _ = b := by ring


-- 5.b
example: ∃ c: ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c:= by
  use -3
  intro x y h
  have hxy: -3 ≤ (x+y) ∧ (x+y) ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc 
      (x + y)^2 ≤ (x + y)^2 + (x - y)^2:= by extra
      _ = 2 * (x ^ 2 + y ^ 2):= by ring
      _ ≤ 2 * 4:= by rel [h]
      _ ≤  3^2:= by numbers
    numbers
  obtain ⟨hl, hr⟩ := hxy
  apply hl  



-- 5.c
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  have h5: 1 ≤ 5 → 5 ≤ 5 → 5 ∣ n := hn 5
  simp at h5
  have h3: 1 ≤ 3 → 3 ≤ 5 → 3 ∣ n := hn 3
  simp at h3
  dsimp [(· ∣ ·)]
  obtain ⟨x, hx⟩ := h3
  obtain ⟨y, hy⟩ := h5
  use 2 * x - 3 * y
  calc
    n = 10 * n - 9 * n := by ring
    _ = 10 * (3 * x) - 9 * n := by rw [hx]
    _ = 10 * (3 * x) - 9 * (5 * y) := by rw [hy]
    _ = 15 * (2 * x - 3 * y) := by ring

  


-- 5.d
example : forall_sufficiently_large x : ℝ, x^3 + 3 * x ≥ 7 * x^2 + 12 := by
  dsimp
  use 10
  intro x hx
  calc
    x^3 + 3 * x 
      = x * x^2 + 3 * x := by ring
    _ ≥ 10 * x^2 + 3 * 10 := by rel [hx]
    _ = 7 * x^2 + 12 + (3 * x^2 + 18) := by ring
    _ ≥ 7 * x^2 + 12 := by extra



---- problem 6
-- 6.a
example {x: ℝ}: x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2:= by
  constructor
  . intro h
    have h1 := calc
      (x+3)*(x-2) =  x ^ 2 + x - 6 := by ring
      _ = 0 := by rw[h]
    rw [mul_eq_zero] at h1
    obtain h2 | h2 := h1
    . left
      addarith [h2]
    . right
      addarith [h2]
  . intro h
    obtain h1 | h1:= h
    . calc
        x ^ 2 + x - 6 = (x + 3) * (x - 2):= by ring
        _ = (-3 + 3) * (x - 2):= by rw[h1]
        _ = 0:= by ring
    . calc 
        x ^ 2 + x - 6 = (x - 2) * (x + 3):= by ring
        _ = (2 - 2) * (x + 3):= by rw[h1]
        _ = 0:= by ring

-- 6.b
example {a: ℤ}: a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3:= by
  constructor
  . intro h
    have ha: -1 ≤ (2 * a - 5) ∧ (2 * a - 5) ≤ 1
    · apply abs_le_of_sq_le_sq'
      calc
        (2 * a - 5)^2 = 4 * a^2 - 2 * 2 * 5 * a + 25 := by ring
        _ = 4 * (a^2 - 5 * a + 5) + 5 := by ring
        _ ≤ 4 * (-1) + 5:= by rel[h]
        _ ≤  1^2 := by numbers
      numbers
    obtain ⟨ h1, h2 ⟩:= ha
    have h3: 2 * 2 ≤ 2 * a:= by   
      calc 
        2 * 2 = - 1 + 3 + 2:= by ring
        _ ≤  (2 * a - 5) + 3 + 2:= by rel[h1]
        _ = 2 * a:= by ring
  
    cancel 2 at h3
    have h4: 2 * a ≤ 2 * 3:= by   
      calc 
        2 * a = (2 * a + - 5) + 5:= by ring
        _ ≤ 1 + 5:= by addarith [h2]
        _ = 2 * 3:= by numbers

    cancel 2 at h4
    interval_cases a
    · left
      numbers 
    · right
      numbers 
  . intro h 
    obtain h1 | h2 := h
    .calc 
      a ^ 2 - 5 * a + 5 ≤ 2 ^ 2 - 5 * 2 + 5:= by rw [h1]
      _ ≤ -1:= by numbers 
    .calc 
      a ^ 2 - 5 * a + 5 ≤ 3 ^ 2 - 5 * 3 + 5:= by rw [h2]
      _ ≤ -1:= by numbers 

