-- Repair for the challenger's objection, which is correct on both points.
-- Core Lean has no real numbers, so the theorem is now stated for an arbitrary
-- power function `pow : R → E → R` with base `a`. Its hypotheses are only the
-- index laws that the book's argument uses: a^(x+y) = a^x · a^y and a^0 = 1.
-- It also assumes injectivity of `x ↦ a^x`, which is what a > 0 and a ≠ 1
-- secure for real powers. Real powers are therefore a special case, including
-- fractional and negative logarithms. Injectivity makes the logarithm unique,
-- so the conclusion says that every logarithm of the product equals the sum.
-- It no longer says only that the sum is some logarithm of the product.

/-- Hall and Knight, Higher Algebra, Art. 204 (logarithm of a product).

Let `pow a x` denote `a^x`, and assume the index laws `a^(x+y) = a^x · a^y`
and `a^0 = 1`. Assume also that `x ↦ a^x` is injective (for real powers this
holds when `a > 0` and `a ≠ 1`). Then by Art. 199/200 `x = log_a N` means
`a^x = N`, and this logarithm is unique.

First part: if `a^x = M` and `a^y = N`, then `x + y` is a logarithm of `MN`,
and every `z` with `a^z = MN` equals `x + y`. That is,
`log_a MN = log_a M + log_a N`.

Second part: the same holds for any number of factors. For a list of pairs
`(M, x)` with `a^x = M`, the sum of the `x` is the logarithm of the product of
the `M`. -/
theorem hk_art_204 {R E : Type} [Mul R] [Add E] [OfNat R 1] [OfNat E 0]
    (pow : R → E → R) (a : R)
    (h_add : ∀ x y : E, pow a (x + y) = pow a x * pow a y)
    (h_zero : pow a 0 = 1)
    (h_inj : ∀ x y : E, pow a x = pow a y → x = y) :
    (∀ (M N : R) (x y : E), pow a x = M → pow a y = N →
      pow a (x + y) = M * N ∧ ∀ z : E, pow a z = M * N → z = x + y) ∧
    (∀ l : List (R × E), (∀ p ∈ l, pow a p.2 = p.1) →
      pow a (l.foldr (fun p acc => p.2 + acc) 0)
          = l.foldr (fun p acc => p.1 * acc) 1 ∧
      ∀ z : E, pow a z = l.foldr (fun p acc => p.1 * acc) 1 →
        z = l.foldr (fun p acc => p.2 + acc) 0) := by
  constructor
  · intro M N x y hx hy
    have h : pow a (x + y) = M * N := by rw [h_add, hx, hy]
    exact ⟨h, fun z hz => h_inj _ _ (hz.trans h.symm)⟩
  · intro l hl
    have key : pow a (l.foldr (fun p acc => p.2 + acc) 0)
        = l.foldr (fun p acc => p.1 * acc) 1 := by
      induction l with
      | nil => exact h_zero
      | cons p t ih =>
        have hp : pow a p.2 = p.1 := hl p (by simp)
        have ht := ih (fun q hq => hl q (by simp [hq]))
        simp only [List.foldr_cons]
        rw [h_add, hp, ht]
    exact ⟨key, fun z hz => h_inj _ _ (hz.trans key.symm)⟩
