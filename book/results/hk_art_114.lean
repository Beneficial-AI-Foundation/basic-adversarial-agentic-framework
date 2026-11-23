/-- Hall & Knight, *Higher Algebra*, Art. 114 (relations between roots and coefficients).

Let `a x^2 + b x + c = 0` be a quadratic equation with `a ≠ 0`. Let `s` be a square root of
the discriminant, so `s * s = b^2 - 4ac`. Put `α = (-b + s) / (2a)` and `β = (-b - s) / (2a)`. Then

* `α` and `β` are roots of the equation: `a α^2 + b α + c = 0` and `a β^2 + b β + c = 0`;
* they are the two roots: `a x^2 + b x + c = a (x - α) (x - β)` for every `x`;
* `α + β = -b / a`, and
* `α * β = c / a`.

The statement is made over an arbitrary field `K` from the core `Lean.Grind.Field` class.
We assume `2 ≠ 0` in `K`, as the root formula itself requires. -/
theorem hk_art_114 {K : Type} [Lean.Grind.Field K] (a b c s : K)
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s * s = b ^ 2 - 4 * a * c) :
    a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 ∧
    a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 ∧
    (∀ x : K, a * x ^ 2 + b * x + c
        = a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a))) ∧
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro x
    grind
  · grind
  · grind
