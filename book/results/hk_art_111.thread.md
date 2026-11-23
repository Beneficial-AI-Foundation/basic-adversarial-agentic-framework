## issue
Issue #111. Art. 111, The Theory of Quadratic Equations
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter IX (The Theory of Quadratic Equations), Art. 111.
The book prints the following text.
After suitable reduction every quadratic equation may be written in the form ax^2 + bx + c = 0 ......(1), and the solution of the equation is x = (−b ± √(b^2 − 4ac))/(2a) ......(2).
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_111.

## prover
/-- Hall & Knight, *Higher Algebra*, Art. 111. Let `a ≠ 0` and let `s` be a square
root of the discriminant, so `s * s = b ^ 2 - 4ac`. Then
`a x ^ 2 + b x + c = 0` holds exactly when `x = (-b ± s) / (2a)`.

Lean core has no real numbers and no square root, so two changes are made.
* The variables range over `Int`.
* The root `√(b ^ 2 - 4ac)` is given as an `s` with `s * s = b ^ 2 - 4ac`.

The formula is stated with the division by `2a` cleared, as `2a·x = -b ± s`.
Since `a ≠ 0`, this is equivalent to `x = (-b ± s) / (2a)`. -/
theorem hk_art_111 (a b c s x : Int) (ha : a ≠ 0) (hs : s * s = b * b - 4 * a * c) :
    a * x * x + b * x + c = 0 ↔ (2 * a * x = -b + s ∨ 2 * a * x = -b - s) := by
  have key : (2 * a * x + b - s) * (2 * a * x + b + s) = 4 * a * (a * x * x + b * x + c) := by
    have h1 : (2 * a * x + b - s) * (2 * a * x + b + s)
        = (2 * a * x + b) * (2 * a * x + b) - s * s := by grind
    rw [h1, hs]
    grind
  generalize hE : a * x * x + b * x + c = E at key ⊢
  generalize ht : 2 * a * x = t at key ⊢
  constructor
  · intro h
    rw [h, Int.mul_zero] at key
    rcases Int.mul_eq_zero.mp key with h1 | h1
    · left; omega
    · right; omega
  · intro h
    have h0 : (t + b - s) * (t + b + s) = 0 := by
      rcases h with h | h
      · have h1 : t + b - s = 0 := by omega
        rw [h1, Int.zero_mul]
      · have h1 : t + b + s = 0 := by omega
        rw [h1, Int.mul_zero]
    rw [key] at h0
    rcases Int.mul_eq_zero.mp h0 with h1 | h1
    · omega
    · exact h1

## lean
Lean accepts the code.

## challenger
OBJECTION: Restricting to `Int` changes what the formula of Art. 111 says. The book gives x = (−b ± √(b² − 4ac))/(2a) for any quadratic, and the division by 2a is the core of that formula. Over `Int`, the hypothesis `s * s = b*b - 4*a*c` cannot be met whenever the discriminant is not a perfect square, as for x² − 2 = 0. The theorem is then vacuous there and covers only equations with integer roots. Lean core provides `Lean.Grind.Field` (and `Rat`), so the claim can be stated over a field of characteristic ≠ 2 with the division `x = (-b ± s) / (2 * a)` written out, rather than cleared over `Int`.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION. The repaired theorem answers my earlier objection. It is stated over an arbitrary `Lean.Grind.Field` with `(2 : α) ≠ 0`, it writes the division `(-b ± s) / (2 * a)` out as the book does, and it no longer rules out non-square discriminants over `Int`. Taking `s` as any element with `s * s = b * b - 4 * a * c` is a faithful encoding of `√(b² − 4ac)`, because the `±` covers both square roots. The biconditional states that the two values are exactly the solutions, which matches "the solution of the equation is …". Lean accepts the code, and I can defend no further objection.

## critic
I argue against merging this pull request, for the following reasons.

1. **The repair moves the vacuity instead of removing it.** The challenger's objection was that the `Int` statement says nothing when the discriminant has no root, as for x² − 2 = 0. The new theorem still assumes an `s` with `s * s = b * b - 4 * a * c`, so the same gap remains in every field that lacks that root.
   - The prover's comment admits this: x² − 2 = 0 is covered only "in every field that has a square root of 8".
   - The project uses Lean core only. `Rat` lacks √8, and core provides no reals, complex numbers or algebraically closed field that would supply one.
   - So no type available to this project makes the theorem say anything about x² − 2 = 0, the challenger's own example. The objection was renamed, not answered. The challenger's "NO OBJECTION" accepted the generalisation without asking for a single non-vacuous instance, such as an `example` with a concrete field and a non-square discriminant.

2. **The statement does not capture what Art. 111 asserts.** The book does not assume a root and then solve. It says that every quadratic is solved by the formula, with √ meaning the square root of whatever b² − 4ac is.
   - Hall & Knight explicitly allow √ of a negative quantity, as imaginary roots in the following articles.
   - The Lean theorem instead makes "a square root of the discriminant exists in α" a premise. That premise is exactly the content the formula supplies.
   - It also silently drops the first half of the article, that every quadratic equation reduces to ax² + bx + c = 0 (1). The theorem only treats equations already in that form.
   - The result is a conditional factorisation lemma, not "the solution of the equation is (2)". Nothing in the docstring flags this weakening. Instead the docstring claims "That is, `x = (-b ± √(b²−4ac))/(2a)`", which overstates the result.

3. **The code rests on unstable internals and is not maintainable.**
   - It is typeclass-parameterised over `Lean.Grind.Field` and calls `Lean.Grind.Field.mul_inv_cancel` and `Lean.Grind.Field.div_eq_mul_inv` directly. These are internal support structures of the `grind` tactic, not a public algebraic API, so the theorem's signature depends on a tactic's implementation details.
   - Nearly every nontrivial step is an opaque `grind` call. This includes the cancellation `calc` steps and `key`.
   - The prover hand-rolls `zd`, a field-has-no-zero-divisors lemma, and `h4` inside the proof rather than stating them as reusable lemmas.
   - Any change to `grind` or to the `Lean.Grind` hierarchy can break both the statement and the proof. Merging a "main theorem" whose type mentions tactic internals sets a poor precedent for the project.

## defender
**Rebuttal to point 1.** The assumption of `s` is not vacuity but the correct mathematics: x² − 2 = 0 has a root in a field exactly when 8 (that is, 4·2) is a square there, so in `Rat` the equation has no solutions and there is nothing true to state. The theorem is non-vacuous in every case where the book's formula produces an element of the field, for example x² − 5x + 6 over `Rat`, and it applies unchanged to ℝ or ℂ as soon as a downstream user supplies a `Lean.Grind.Field` instance.

**Rebuttal to point 2.** The book's formula (2) itself presupposes that √(b² − 4ac) denotes something, and the docstring says plainly that `s` is a square root of the discriminant. Quantifying over all fields covers the imaginary case in any field that contains such roots, with ℂ the intended example. "After suitable reduction…" is a remark about rewriting equations, not a theorem; the asserted result is (1) ⇔ (2), which the biconditional states exactly with the division written out.

**Rebuttal to point 3.** `Lean.Grind.Field` is the only field abstraction that Lean core provides, and the issue requires core only, so using it is the only option, not a precedent. The proof is checked by Lean. Inline helpers such as `zd` and the `grind` steps affect style rather than correctness, and they are no reason to block a correct, faithful theorem.

## supervisor
MERGE. Lean accepts the final code, and the statement matches Art. 111: over any core field with `2 ≠ 0` and `a ≠ 0`, with `s` a square root of `b² − 4ac`, the quadratic vanishes exactly when `x = (-b ± s)/(2a)`, with the division written out. The critic's first two points fail because a missing square root in `α` means there is no root to describe, which is what the book's √ presupposes, and "after suitable reduction" is a remark rather than a separate claim. The third point concerns style and the only field abstraction that core offers, so it does not affect correctness or faithfulness.
