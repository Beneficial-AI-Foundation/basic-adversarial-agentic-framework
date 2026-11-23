/-- Hall & Knight, *Higher Algebra*, Art. 55: let `a` be the first term, `r ≠ 1` the
common ratio and `n` the number of terms of a geometrical progression. Then the sum
`s = a + a r + a r^2 + ... + a r^(n-1)` satisfies
`s = a (r^n - 1) / (r - 1)` (formula (1)) and `s = a (1 - r^n) / (1 - r)` (formula (2)).

The statement holds over an arbitrary field `α`, given by core's `Lean.Grind.Field`, so
`/` is true field division. This covers rational and real quantities, and also
decreasing progressions such as `1, 1/2, 1/4, ...`. -/
def gpSum {α : Type u} [Lean.Grind.Field α] (a r : α) : Nat → α
  | 0 => 0
  | n + 1 => gpSum a r n + a * r ^ n

theorem gpSum_mul {α : Type u} [Lean.Grind.Field α] (a r : α) (n : Nat) :
    gpSum a r n * (r - 1) = a * (r ^ n - 1) := by
  induction n with
  | zero =>
    simp only [gpSum]
    rw [Lean.Grind.Semiring.pow_zero]
    grind
  | succ n ih =>
    simp only [gpSum]
    rw [Lean.Grind.Semiring.pow_succ]
    grind

/-- Hall & Knight, Art. 55: over any field, for `r ≠ 1`, the sum
`s = a + a r + ... + a r^(n-1)` of `n` terms of a geometrical progression satisfies
`s = a (r^n - 1)/(r - 1)` and `s = a (1 - r^n)/(1 - r)`. -/
theorem hk_art_55 {α : Type u} [Lean.Grind.Field α] (a r : α) (n : Nat) (hr : r ≠ 1) :
    gpSum a r n = a * (r ^ n - 1) / (r - 1) ∧
    gpSum a r n = a * (1 - r ^ n) / (1 - r) := by
  have h := gpSum_mul a r n
  have h1 : r - 1 ≠ 0 := by
    intro h0
    apply hr
    grind
  have h2 : 1 - r ≠ 0 := by
    intro h0
    apply hr
    grind
  constructor
  · grind
  · grind
