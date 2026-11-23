-- Response to the second objection. The objection is right, and the statement is repaired as follows.
-- 1. The index law `(b^x)^y = b^(x*y)` is now assumed only for positive bases (`Pos b`).
--    It is false for negative bases under real powers, as the objection notes.
-- 2. `ValidBase` is tied to positivity by `base_pos : ValidBase a → Pos a`.
--    In the intended model, `Pos b` means `b > 0` and `ValidBase a` means `a > 0 ∧ a ≠ 1`.
-- 3. Lean core has no real numbers, real powers or real logarithms, so the model stays
--    abstract. Each hypothesis is now a true property of positive reals under real powers:
--    * the index law for `b > 0`;
--    * commutativity of real multiplication;
--    * `b > 0 → b^x > 0`;
--    * `a^(log_a n) = n` for `a > 0`, `a ≠ 1` and `n > 0` (the definition of Art. 199);
--    * injectivity of `x ↦ a^x` for `a > 0`, `a ≠ 1`, which is the uniqueness of logarithms.
--    These facts are what make `log_a` well defined in Art. 199, and the book takes them
--    for granted. The theorem derives the equality of logarithm values from them.

/-- Art. 206 (Hall and Knight, Higher Algebra): for a valid base `a` (`a > 0`,
`a ≠ 1`) and a positive number `M`, `log_a (M^p) = p · log_a M` for every index
`p`, and in particular `log_a (M^(1/r)) = (1/r) · log_a M`.

Powers `pow b x` (standing for `b^x`) and logarithms `log a n` are given abstractly.
The intended model has `Pos b` meaning `b > 0` and `ValidBase a` meaning
`a > 0 ∧ a ≠ 1`. The hypotheses are all true in that model:
* the index law `(b^x)^y = b^(x*y)` for positive `b`;
* commutativity of index multiplication;
* a valid base is positive;
* powers of a positive number are positive;
* the defining property `a^(log_a n) = n` (Art. 199) for a valid base `a` and a positive `n`;
* injectivity of `x ↦ a^x` for a valid base `a`, which is the uniqueness of logarithms. -/
theorem hk_art_206 {N E : Type} [Mul E] [Div E] [OfNat E 1]
    (pow : N → E → N) (log : N → N → E)
    (Pos : N → Prop) (ValidBase : N → Prop)
    (index_law : ∀ (b : N) (x y : E), Pos b → pow (pow b x) y = pow b (x * y))
    (hcomm : ∀ x y : E, x * y = y * x)
    (base_pos : ∀ a : N, ValidBase a → Pos a)
    (pow_pos : ∀ (b : N) (x : E), Pos b → Pos (pow b x))
    (log_spec : ∀ a n : N, ValidBase a → Pos n → pow a (log a n) = n)
    (log_unique : ∀ (a : N) (x y : E), ValidBase a → pow a x = pow a y → x = y)
    (a M : N) (ha : ValidBase a) (hM : Pos M) :
    (∀ p : E, log a (pow M p) = p * log a M) ∧
    (∀ r : E, log a (pow M (1 / r)) = (1 / r) * log a M) := by
  constructor
  · intro p
    apply log_unique a _ _ ha
    rw [log_spec a _ ha (pow_pos M p hM)]
    rw [hcomm p (log a M), ← index_law a (log a M) p (base_pos a ha),
      log_spec a M ha hM]
  · intro r
    apply log_unique a _ _ ha
    rw [log_spec a _ ha (pow_pos M (1 / r) hM)]
    rw [hcomm (1 / r) (log a M), ← index_law a (log a M) (1 / r) (base_pos a ha),
      log_spec a M ha hM]
