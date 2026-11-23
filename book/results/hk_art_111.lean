-- The objection holds, and the code is repaired. The theorem is now stated over any field
-- in which `2 ≠ 0`, using the class `Lean.Grind.Field` from Lean core. The quotient
-- `(-b ± s) / (2 * a)` is written out as in the book. It is no longer cleared over `Int`.
-- Equations such as x^2 - 2 = 0 are now covered in every field that has a square root of 8.

/-- Hall & Knight, *Higher Algebra*, Art. 111. Let `α` be a field of characteristic
other than 2, which means `(2 : α) ≠ 0`. Let `a ≠ 0`, and let `s` be a square root of the
discriminant, so `s * s = b * b - 4 * a * c`. Then `a x ^ 2 + b x + c = 0` holds exactly
when `x = (-b + s) / (2a)` or `x = (-b - s) / (2a)`. That is,
`x = (-b ± √(b ^ 2 - 4ac)) / (2a)`. -/
theorem hk_art_111 {α : Type} [Lean.Grind.Field α] (a b c s x : α)
    (h2 : (2 : α) ≠ 0) (ha : a ≠ 0) (hs : s * s = b * b - 4 * a * c) :
    a * x * x + b * x + c = 0 ↔ (x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a)) := by
  have i2 : (2 : α) * 2⁻¹ = 1 := Lean.Grind.Field.mul_inv_cancel h2
  have hD : (2 : α) * a ≠ 0 := by
    intro h
    apply ha
    calc a = 2⁻¹ * (2 * a) := by grind
      _ = 0 := by rw [h]; grind
  have iD : (2 * a) * (2 * a)⁻¹ = 1 := Lean.Grind.Field.mul_inv_cancel hD
  have zd : ∀ u v : α, u * v = 0 → u = 0 ∨ v = 0 := by
    intro u v h
    by_cases hu : u = 0
    · exact Or.inl hu
    · right
      have iu : u * u⁻¹ = 1 := Lean.Grind.Field.mul_inv_cancel hu
      calc v = u⁻¹ * (u * v) := by grind
        _ = 0 := by rw [h]; grind
  have key : (2 * a * x + b - s) * (2 * a * x + b + s) = 4 * a * (a * x * x + b * x + c) := by
    grind
  have h4 : (4 : α) * a ≠ 0 := by
    intro h
    have : (2 : α) * (2 * a) = 0 := by rw [← h]; grind
    rcases zd _ _ this with h' | h'
    · exact h2 h'
    · exact hD h'
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Field.div_eq_mul_inv]
  constructor
  · intro h
    have k0 : (2 * a * x + b - s) * (2 * a * x + b + s) = 0 := by rw [key, h]; grind
    rcases zd _ _ k0 with h1 | h1
    · left
      calc x = (2 * a)⁻¹ * (2 * a * x) := by grind
        _ = (-b + s) * (2 * a)⁻¹ := by grind
    · right
      calc x = (2 * a)⁻¹ * (2 * a * x) := by grind
        _ = (-b - s) * (2 * a)⁻¹ := by grind
  · intro h
    have k0 : (2 * a * x + b - s) * (2 * a * x + b + s) = 0 := by
      rcases h with h | h
      · have h1 : 2 * a * x + b - s = 0 := by rw [h]; grind
        rw [h1]; grind
      · have h1 : 2 * a * x + b + s = 0 := by rw [h]; grind
        rw [h1]; grind
    rw [key] at k0
    rcases zd _ _ k0 with h1 | h1
    · exact absurd h1 h4
    · exact h1
