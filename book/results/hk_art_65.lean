-- Reply to the objection: the point holds and the statement is revised.
-- The Int version only covered pairs where `(a+b)/2`, `√(ab)` and `2ab/(a+b)` happen to be
-- integers, so it was a narrower special case and did not state the article's claim.
-- The core library offers no stable field class or real numbers to rely on. The theorem is
-- therefore stated over an arbitrary type `α` carrying `+`, `*` and `2`. It assumes only
-- the algebraic laws the argument uses:
--   * multiplication is commutative and associative,
--   * `2` can be cancelled, which holds in any field of characteristic ≠ 2 such as ℚ or ℝ.
-- In such a field, `2A = a + b` is the same as `A = (a+b)/2`. When `a + b ≠ 0`,
-- `H(a+b) = 2ab` is the same as `H = 2ab/(a+b)`. `G` is any square root of `ab`, so `√(ab)`
-- is covered whenever it exists. So the result now covers general `a` and `b`.

/-- Hall and Knight, Higher Algebra, Art. 65. Let `A`, `G`, `H` be the arithmetic, geometric
and harmonic means between `a` and `b`. These are `A = (a+b)/2`, `G = √(ab)` and
`H = 2ab/(a+b)`. Then `A * H = G ^ 2`, that is, `G` is the geometric mean between `A` and `H`.

The quantities live in any type `α` with commutative, associative multiplication in which
`2` can be cancelled. This includes ℚ, ℝ, or any field of characteristic ≠ 2. Each mean is
given by its defining equation with the division cleared:
* `2 * A = a + b` stands for `A = (a + b) / 2`,
* `G * G = a * b` stands for `G = √(ab)`,
* `H * (a + b) = 2 * a * b` stands for `H = 2ab / (a + b)`, which needs `a + b ≠ 0`.

The conclusion `A * H = G * G` is the book's `AH = ab = G²`. -/
theorem hk_art_65 {α : Type} [Add α] [Mul α] [OfNat α 2] [OfNat α 0]
    (mul_comm : ∀ x y : α, x * y = y * x)
    (mul_assoc : ∀ x y z : α, x * y * z = x * (y * z))
    (two_cancel : ∀ x y : α, (2 : α) * x = 2 * y → x = y)
    (a b A G H : α) (hs : a + b ≠ 0)
    (hA : 2 * A = a + b) (hH : H * (a + b) = 2 * a * b) (hG : G * G = a * b) :
    A * H = G * G := by
  apply two_cancel
  calc (2 : α) * (A * H) = (2 * A) * H := (mul_assoc 2 A H).symm
    _ = (a + b) * H := by rw [hA]
    _ = H * (a + b) := mul_comm _ _
    _ = 2 * a * b := hH
    _ = 2 * (a * b) := mul_assoc _ _ _
    _ = 2 * (G * G) := by rw [hG]
