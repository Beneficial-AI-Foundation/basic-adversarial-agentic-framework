-- Revision for the supervisor's second REVISE:
-- 1. Removed the stale header that said the code had not been run through the checker.
-- 2. In `natElt_rat`, replaced the `first | grind | simp | exact …` combinator with a single
--    `grind`, the same tactic that closes the zero case of that lemma.
-- 3. Dropped the unused bridge lemma `natElt_eq_natCast` and its `local instance` attribute.
--    `natElt_rat` remains the bridge that `hk_art_40_rat` uses.
-- 4. Added a check with nonzero sum: a = 3/4, d = -1/2, n = 3, l = -1/4.
--    The terms are 3/4, 1/4, -1/4, so the sum is 3/4, and both formulas give 3/4.
--    Unlike the n = 4 progression, here a + l ≠ 0, so this check tests the factor n/2.

universe u

/-- The natural number `n` as an element of the ring `α`: `0 + 1 + … + 1` (n ones). -/
def natElt {α : Type u} [Lean.Grind.CommRing α] : Nat → α
  | 0 => 0
  | n + 1 => natElt n + 1

/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms:
`apSum a d n = a + (a + d) + … + (a + (n - 1) d)`. -/
def apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : Nat → α
  | 0 => 0
  | n + 1 => apSum a d n + (a + natElt n * d)

theorem two_apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : ∀ n : Nat,
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d)
  | 0 => by simp only [apSum, natElt]; grind
  | n + 1 => by
    have ih := two_apSum a d n
    simp only [apSum, natElt]
    grind

/-- Hall & Knight, Higher Algebra, Art. 40, over an arbitrary commutative ring.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Here `natElt n` is `n` as an element of the ring (over `Rat`, see `natElt_rat`).
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
These are stated in the doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`.
The printed form over `Rat` is `hk_art_40_rat`. -/
theorem hk_art_40 {α : Type u} [Lean.Grind.CommRing α] (a d l : α) (n : Nat)
    (hl : l = a + (natElt n - 1) * d) :
    2 * apSum a d n = natElt n * (a + l) ∧
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d) := by
  subst hl
  have h := two_apSum a d n
  exact ⟨by grind, h⟩

/-- `natElt n` is the usual rational number `n`. -/
theorem natElt_rat (n : Nat) : (natElt n : Rat) = (n : Rat) := by
  induction n with
  | zero => simp only [natElt]; grind
  | succ n ih =>
    simp only [natElt]
    rw [ih]
    grind

/-- Hall & Knight, Art. 40, over `Rat`, in the printed form:
with `l = a + (n - 1) d` (2), the sum `s` of the `n` terms satisfies
`s = (n/2)(a + l)` (1) and `s = (n/2){2a + (n - 1) d}` (3). -/
theorem hk_art_40_rat (a d l : Rat) (n : Nat) (hl : l = a + ((n : Rat) - 1) * d) :
    apSum a d n = ((n : Rat) / 2) * (a + l) ∧
    apSum a d n = ((n : Rat) / 2) * (2 * a + ((n : Rat) - 1) * d) := by
  have hb := natElt_rat n
  have h := hk_art_40 a d l n (by rw [hb]; exact hl)
  rw [hb] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · grind
  · grind

/-- The book-style progression `3/4, 1/4, -1/4, -3/4` (a = 3/4, d = -1/2, n = 4, l = -3/4):
formula (1) applies and gives the sum 0. -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).1
  rw [h]
  grind

/-- The same progression through formula (3). -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).2
  rw [h]
  grind

/-- A nonzero-sum check: `3/4, 1/4, -1/4` (a = 3/4, d = -1/2, n = 3, l = -1/4).
Formula (1) gives `(3/2)(3/4 - 1/4) = 3/4`. -/
example : apSum (3/4 : Rat) (-1/2) 3 = 3/4 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-1/4) 3 (by grind)).1
  rw [h]
  grind

/-- The same progression through formula (3): `(3/2)(3/2 + 2·(-1/2)) = 3/4`. -/
example : apSum (3/4 : Rat) (-1/2) 3 = 3/4 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-1/4) 3 (by grind)).2
  rw [h]
  grind
