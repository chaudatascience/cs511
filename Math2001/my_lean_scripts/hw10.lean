import Mathlib.Data.Real.Basic
import Library.Theory.Parity
import Library.Theory.Comparison
import Library.Theory.Prime
import Mathlib.Tactic.Set
import Mathlib.Tactic.IntervalCases
import Library.Tactic.Induction
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Use
import Mathlib.Tactic.GCongr
import Library.Tactic.Cancel

def fmod (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fmod (n + d) d
  else if h2 : 0 < d * (n - d) then
    fmod (n - d) d
  else if h3 : n = d then
    0
  else
    n
termination_by _ n d => 2 * n - d

def fdiv (n d : ℤ) : ℤ :=
  if n * d < 0 then
    fdiv (n + d) d - 1
  else if 0 < d * (n - d) then
    fdiv (n - d) d + 1
  else if h3 : n = d then
    1
  else
    0
termination_by _ n d => 2 * n - d

theorem fmod_add_fdiv (n d : ℤ) : fmod n d + d * fdiv n d = n := by
  rw [fdiv, fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_add_fdiv (n + d) d -- inductive hypothesis
    calc fmod (n + d) d + d * (fdiv (n + d) d - 1)
        = (fmod (n + d) d + d * fdiv (n + d) d) - d := by ring
      _ = (n + d) - d := by rw [IH]
      _ = n := by ring
  · -- case `0 < d * (n - d)`
    have IH := fmod_add_fdiv (n - d) d -- inductive hypothesis
    calc fmod (n - d) d + d * (fdiv (n - d) d + 1)
        = (fmod (n - d) d + d * fdiv (n - d) d) + d := by ring
        _ = n := by addarith [IH]
  · -- case `n = d`
    calc 0 + d * 1 = d := by ring
      _ = n := by rw [h3]
  · -- last case
    ring
termination_by _ n d => 2 * n - d

theorem fmod_nonneg_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : 0 ≤ fmod n d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_nonneg_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_nonneg_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    extra
  · -- last case
    cancel d at h1
termination_by _ n d hd => 2 * n - d

theorem fmod_lt_of_pos (n : ℤ) {d : ℤ} (hd : 0 < d) : fmod n d < d := by
  rw [fmod]
  split_ifs with h1 h2 h3 <;> push_neg at *
  · -- case `n * d < 0`
    have IH := fmod_lt_of_pos (n + d) hd -- inductive hypothesis
    apply IH
  · -- case `0 < d * (n - d)`
    have IH := fmod_lt_of_pos (n - d) hd -- inductive hypothesis
    apply IH
  · -- case `n = d`
    apply hd
  · -- last case
    have h4 :=
    calc 0 ≤ - d * (n - d) := by addarith [h2]
      _ = d * (d - n) := by ring
    cancel d at h4
    apply lt_of_le_of_ne
    · addarith [h4]
    · apply h3
termination_by _ n d hd => 2 * n - d

def T (n : ℤ) : ℤ :=
  if 0 < n then
    T (1 - n) + 2 * n - 1
  else if 0 < - n then
    T (-n)
  else
    0
termination_by T n => 3 * n - 1

/- 5 points -/
theorem problem4a (n : ℤ) : T n = n ^ 2 := by
  rw [T]
  split_ifs with h1 h2 <;> push_neg at *
  ·
    have IH := problem4a (1 - n)
    calc
      T (1 - n) + 2 * n - 1
        = (1 - n)^2 + 2 * n - 1 := by rw [IH]
      _ = 1 - 2 * n + n^2 + 2 * n - 1 := by ring
      _ = n^2 := by ring
  . have IH := problem4a (-n)
    calc
      T (-n)
        = (-n)^2 := by rw [IH]
      _ = n^2 := by ring
  . have h3 : n = 0 := by linarith
    rw [h3]
    ring
  termination_by _ n => 3 * n - 1


/- Hint:  prove uniqueness, then use it to prove problem4b -/
theorem uniqueness (a b : ℤ) (h: 0 < b) {r s: ℤ}
    (hr: 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b])
    (hs: 0 ≤ s ∧ s < b ∧ a ≡ s [ZMOD b]): r = s := by
    obtain ⟨hr1, hr2, hr3⟩ := hr
    obtain ⟨hs1, hs2, hs3⟩ := hs
    dsimp [(·∣·)] at hr3
    dsimp [(·∣·)] at hs3
    obtain ⟨c, hc⟩ := hr3
    obtain ⟨d, hd⟩ := hs3
    have h1: b * c > b * (d - 1) := by
      calc
        b * c = a - r := by rw [hc]
        _ > a - b := by rel [hr2]
        _ = a - s + s - b := by ring
        _ = b * d + s - b := by rw [hd]
        _ ≥ b * d - b := by extra
        _ = b * (d - 1) := by ring
    have h2: b * c < b * (d + 1) := by
      calc
        b * c = a - r := by rw [hc]
        _ = a - s + s - r:= by ring
        _ = b * d + s - r := by rw [hd]
        _ ≤ b * d + s - 0 := by rel [hr1]
        _ = b * d + s := by ring
        _ < b * d + b := by rel [hs2]
        _ = b * (d + 1) := by ring
    cancel b at h1
    cancel b at h2
    have h3: c = d := by addarith [h1, h2]
    have h4: a-r = a-s := by
      calc
        a - r = b * c := by rw [hc]
        _ = b * d := by rw [h3]
        _ = a -s := by rw [hd]
    have h5: r = s := by addarith [h4]
    apply h5

/- 5 points -/
theorem problem4b (a b : ℤ) (h : 0 < b) : ∃! r : ℤ, 0 ≤ r ∧ r < b ∧ a ≡ r [ZMOD b] := by
  use fmod a b
  dsimp
  constructor
  . constructor
    . apply fmod_nonneg_of_pos a h
    . constructor
      . apply fmod_lt_of_pos a h
      . use fdiv a b
        have Hab: fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
        addarith [Hab]
  . intro r hr
    have hCond: 0 ≤ fmod a b ∧ fmod a b < b ∧ a ≡ fmod a b [ZMOD b] := by
      constructor
      . apply fmod_nonneg_of_pos a h
      . constructor
        . apply fmod_lt_of_pos a h
        . use fdiv a b
          have Hab: fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
          addarith [Hab]
    have h1:= by apply uniqueness a b h hCond hr
    rw [h1]




@[decreasing] theorem lower_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : -b < fmod a b := by
  have H : 0 ≤ fmod a b
  · apply fmod_nonneg_of_pos
    apply h1
  calc -b < 0 := by addarith [h1]
    _ ≤ _ := H

@[decreasing] theorem lower_bound_fmod2 (a b : ℤ) (h1 : b < 0) : b < fmod a (-b) := by
  have H : 0 ≤ fmod a (-b)
  · apply fmod_nonneg_of_pos
    addarith [h1]
  have h2 : 0 < -b := by addarith [h1]
  calc b < 0 := h1
    _ ≤ fmod a (-b) := H

@[decreasing] theorem upper_bound_fmod2 (a b : ℤ) (h1 : b < 0) : fmod a (-b) < -b := by
  apply fmod_lt_of_pos
  addarith [h1]

@[decreasing] theorem upper_bound_fmod1 (a b : ℤ) (h1 : 0 < b) : fmod a b < b := by
  apply fmod_lt_of_pos
  apply h1

def gcd (a b : ℤ) : ℤ :=
  if 0 < b then
    gcd b (fmod a b)
  else if b < 0 then
    gcd b (fmod a (-b))
  else if 0 ≤ a then
    a
  else
    -a
termination_by _ a b => b

/- 5 points -/
theorem problem5a (a b : ℤ) : gcd a b ∣ b ∧ gcd a b ∣ a := by
  rw [gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH : _ ∧ _ := problem5a b (fmod a b) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      apply IH_left
    · -- prove that `gcd a b ∣ a`
      obtain ⟨k, hk⟩ := IH_left
      obtain ⟨l, hl⟩ := IH_right
      use (l + k * fdiv a b)
      have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
      set q := fdiv a b
      set r := fmod a b
      calc
        a = r + b * q := by rw [H]
        _ = gcd b r * l + (gcd b r * k) * q := by rw [← hk, ← hl]
        _ = gcd b r * (l + k * q) := by ring
  · -- case `b < 0`
    have IH : _ ∧ _ := problem5a b (fmod a (-b)) -- inductive hypothesis
    obtain ⟨IH_right, IH_left⟩ := IH
    constructor
    · -- prove that `gcd a b ∣ b`
      apply IH_left
    · -- prove that `gcd a b ∣ a`
      obtain ⟨k, hk⟩ := IH_left
      obtain ⟨l, hl⟩ := IH_right
      have H := fmod_add_fdiv a (-b)
      use l - k * fdiv a (-b)
      set q := fdiv a (-b)
      set r := fmod a (-b)
      calc a = r + (-b) * q := by rw [H]
      _ = gcd b r * l + (- (gcd b r * k)) * q := by rw [← hk, ← hl]
      _ = gcd b r * (l - k * q) := by ring
  · -- case `b = 0`, `0 ≤ a`
    constructor
    · -- prove that `gcd a b ∣ b`
      have hb: b = 0 := le_antisymm h1 h2
      use 0
      calc
        b = 0 := hb
        _ = a * 0 := by ring
    · -- prove that `gcd a b ∣ a`
      use 1
      ring
  · -- case `b = 0`, `a < 0`
    constructor
    · -- prove that `gcd a b ∣ b`
      have hb: b = 0 := le_antisymm h1 h2
      use 0
      calc
        b = 0 := hb
        _ = -a * 0 := by ring
    · -- prove that `gcd a b ∣ a`
      use -1
      ring
termination_by problem5a a b => b

mutual

def L (a b : ℤ) : ℤ :=
  if 0 < b then
    R b (fmod a b)
  else if b < 0 then
    R b (fmod a (-b))
  else if 0 ≤ a then
    1
  else
    -1

def R (a b : ℤ) : ℤ :=
  if 0 < b then
    L b (fmod a b) - (fdiv a b) * R b (fmod a b)
  else if b < 0 then
    L b (fmod a (-b)) + (fdiv a (-b)) * R b (fmod a (-b))
  else
    0

end
termination_by L a b => b ; R a b => b

#eval L (-21) 15 -- infoview displays `2`
#eval R (-21) 15 -- infoview displays `3`

theorem L_mul_add_R_mul (a b : ℤ) : L a b * a + R a b * b = gcd a b := by
  rw [R, L, gcd]
  split_ifs with h1 h2 <;> push_neg at *
  · -- case `0 < b`
    have IH := L_mul_add_R_mul b (fmod a b) -- inductive hypothesis
    have H : fmod a b + b * fdiv a b = a := fmod_add_fdiv a b
    set q := fdiv a b
    set r := fmod a b
    calc R b r * a + (L b r - q * R b r) * b
        = R b r * (r + b * q) + (L b r - q * R b r) * b:= by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b < 0`
    have IH := L_mul_add_R_mul b (fmod a (-b)) -- inductive hypothesis
    have H : fmod a (-b) + (-b) * fdiv a (-b) = a := fmod_add_fdiv a (-b)
    set q := fdiv a (-b)
    set r := fmod a (-b)
    calc  R b r * a + (L b r + q * R b r) * b
        =  R b r * (r + -b * q) + (L b r + q * R b r) * b := by rw [H]
      _ = L b r * b + R b r * r := by ring
      _ = gcd b r := IH
  · -- case `b = 0`, `0 ≤ a`
    ring
  · -- case `b = 0`, `a < 0`
    ring
termination_by L_mul_add_R_mul a b => b

#eval L 7 5 -- infoview displays `-2`
#eval R 7 5 -- infoview displays `3`
#eval gcd 7 5 -- infoview displays `1`

theorem bezout (a b : ℤ) : ∃ x y : ℤ, x * a + y * b = gcd a b := by
  use L a b, R a b
  apply L_mul_add_R_mul

/- 5 points -/
theorem problem5b {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ gcd a b := by
  have h1 := by apply bezout a b
  obtain ⟨x, y, h2⟩ := h1
  obtain ⟨m, hk⟩ := ha
  obtain ⟨n, hl⟩ := hb
  have h3: d ∣ x * a + y * b := by
    use x * m + y * n
    calc
      x * a + y * b = x * (d * m ) + y * (d * n) := by rw [hk, hl]
      _ = d * (x * m + y * n) := by ring
  rw [h2] at h3
  apply h3
