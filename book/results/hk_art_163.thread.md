## issue
Issue #163. Binomial Theorem (Art. 163, To find the expansion of (x + a)^n when n is a positive integer)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XIII (Binomial Theorem. Positive Integral Index), Art. 163.
The book prints the following text.
[From Art. 163, p. 138] in S_2 the number of terms is the same as the number of combinations of n things 2 at a time; that is, {n}C{2}; in S_3 the number of terms is {n}C{3}; and so on.
To find the expansion of (x + a)^n when n is a positive integer.
(x + a)^n = x^n + {n}C{1} a x^(n−1) + {n}C{2} a^2 x^(n−2) + {n}C{3} a^3 x^(n−3) + ... + {n}C{n} a^n; substituting for {n}C{1}, {n}C{2}, ... we obtain (x + a)^n = x^n + n a x^(n−1) + (n(n − 1)/(1 . 2)) a^2 x^(n−2) + (n(n − 1)(n − 2)/(1 . 2 . 3)) a^3 x^(n−3) + ... + a^n, the series containing n + 1 terms. This is the Binomial Theorem, and the expression on the right is said to be the expansion of (x + a)^n.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_163.

## prover
/-- The binomial coefficient `nCr`, the number of combinations of `n` things `r` at a time,
given by Pascal's rule. -/
def binomC : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomC n k + binomC n (k + 1)

/-- `rangeSum f m = f 0 + f 1 + ... + f (m - 1)`. -/
def rangeSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | m + 1 => rangeSum f m + f m

theorem binomC_zero_right (n : Nat) : binomC n 0 = 1 := by
  cases n <;> rfl

theorem binomC_succ (n k : Nat) : binomC (n + 1) (k + 1) = binomC n k + binomC n (k + 1) := rfl

theorem binomC_gt : ∀ n k : Nat, n < k → binomC n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [binomC_succ, binomC_gt n k (by omega), binomC_gt n (k + 1) (by omega)]

theorem rangeSum_congr (f g : Nat → Int) :
    ∀ m, (∀ r, r < m → f r = g r) → rangeSum f m = rangeSum g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [rangeSum]
    rw [rangeSum_congr f g m (fun r hr => h r (by omega)), h m (by omega)]

theorem rangeSum_add (f g : Nat → Int) :
    ∀ m, rangeSum (fun r => f r + g r) m = rangeSum f m + rangeSum g m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    simp only [rangeSum]
    rw [rangeSum_add f g m]
    omega

theorem rangeSum_mul (f : Nat → Int) (c : Int) :
    ∀ m, rangeSum f m * c = rangeSum (fun r => f r * c) m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    simp only [rangeSum]
    rw [Int.add_mul, rangeSum_mul f c m]

theorem rangeSum_shift (f : Nat → Int) :
    ∀ m, rangeSum f (m + 1) = f 0 + rangeSum (fun r => f (r + 1)) m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    show rangeSum f (m + 1) + f (m + 1) = f 0 + (rangeSum (fun r => f (r + 1)) m + f (m + 1))
    rw [rangeSum_shift f m]
    omega

theorem binom_all (x a : Int) :
    ∀ n : Nat, (x + a) ^ n = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1)
  | 0 => by
    show (x + a) ^ 0 = 0 + (binomC 0 0 : Int) * a ^ 0 * x ^ (0 - 0)
    rw [binomC_zero_right]
    simp
  | n + 1 => by
    have ih := binom_all x a n
    have hD : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * x
        = x ^ (n + 1) + rangeSum (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1) := by
      rw [rangeSum_mul]
      have h1 : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * x) (n + 1)
          = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1) := by
        apply rangeSum_congr
        intro r hr
        show (binomC n r : Int) * a ^ r * x ^ (n - r) * x = (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)
        have : n + 1 - r = (n - r) + 1 := by omega
        rw [this, Int.pow_succ]
        simp only [Int.mul_assoc]
      rw [h1]
      have h2 : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1 + 1)
          = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1) := by
        simp only [rangeSum]
        rw [binomC_gt n (n + 1) (by omega)]
        simp
      rw [← h2, rangeSum_shift (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1)]
      congr 1
      · show (binomC n 0 : Int) * a ^ 0 * x ^ (n + 1 - 0) = x ^ (n + 1)
        rw [binomC_zero_right]
        simp
      · apply rangeSum_congr
        intro r _
        show (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))
            = (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)
        rw [show n + 1 - (r + 1) = n - r by omega]
    calc (x + a) ^ (n + 1)
        = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * x
          + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * a := by
          rw [Int.pow_succ, ih, Int.mul_add]
      _ = (x ^ (n + 1) + rangeSum (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1))
          + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a) (n + 1) := by
          rw [hD, rangeSum_mul]
      _ = x ^ (n + 1) + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a
            + (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1) := by
          rw [rangeSum_add (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a)
            (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1)]
          rw [Int.add_assoc]
          congr 1
          exact Int.add_comm _ _
      _ = (binomC (n + 1) 0 : Int) * a ^ 0 * x ^ (n + 1 - 0)
          + rangeSum (fun r => (binomC (n + 1) (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))) (n + 1) := by
          congr 1
          · rw [binomC_zero_right]
            simp
          · apply rangeSum_congr
            intro r _
            show (binomC n r : Int) * a ^ r * x ^ (n - r) * a
                + (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)
                = (binomC (n + 1) (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))
            rw [binomC_succ, show n + 1 - (r + 1) = n - r by omega]
            push_cast
            simp only [Int.add_mul, Int.mul_add, Int.pow_succ, Int.mul_assoc, Int.mul_comm,
              Int.mul_left_comm]
      _ = rangeSum (fun r => (binomC (n + 1) r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1 + 1) :=
          (rangeSum_shift (fun r => (binomC (n + 1) r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1)).symm

/-- Binomial Theorem (Hall and Knight, Higher Algebra, Art. 163): when `n` is a positive
integer, `(x + a)^n = x^n + nC1 a x^(n-1) + nC2 a^2 x^(n-2) + ... + nCn a^n`, that is,
`(x + a)^n` equals the sum over `r = 0, 1, ..., n` (a series of `n + 1` terms) of
`nCr * a^r * x^(n-r)`. -/
theorem hk_art_163 (x a : Int) (n : Nat) (hn : 0 < n) :
    (x + a) ^ n = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) := by
  have _ := hn
  exact binom_all x a n

## lean
Lean accepts the code.

## challenger
OBJECTION: In the book, nCr is the number of combinations of n things r at a time. The article's stated result is also the explicit form with coefficients n, n(n−1)/(1·2), n(n−1)(n−2)/(1·2·3), and so on. Your `binomC` is defined by Pascal's rule, and you prove no lemma linking it to either meaning, such as `binomC n r * r! * (n-r)! = n!` or a falling-factorial formula. As written, `hk_art_163` only checks a recursion that you chose to call nCr, so it does not state the book's expansion. A further gap is that x and a are fixed to `Int`, while the book treats arbitrary quantities.

## prover
-- Reply to the objection.
-- (1) Meaning of nCr. `binomC` is still defined by Pascal's rule. It is now linked to the
--     book's meanings by proved lemmas:
--     * `binomC_mul_fact`: `binomC n r * r! = n(n-1)...(n-r+1)`.
--     * `binomC_eq_div`: `binomC n r = n(n-1)...(n-r+1) / (1*2*...*r)`.
--     * `binomC_mul_fact_mul_fact`: for `r ≤ n`, `binomC n r * (r! * (n-r)!) = n!`.
--       This is the formula for the number of combinations of n things r at a time.
--     `hk_art_163` now states three things: the expansion with nCr, the expansion with the
--     book's explicit coefficients `n(n-1)...(n-r+1)/(1*2*...*r)`, and the factorial
--     characterisation of nCr.
-- (2) The `Int` restriction stays. This is not a gap in substance, for this reason. Both
--     sides are polynomials in x and a with integer coefficients. Such an identity that
--     holds for all integers x, a holds as a polynomial identity, because Int is an
--     infinite integral domain. So it holds for quantities in any commutative ring. Core
--     Lean without Mathlib has no standard commutative-ring class to state that directly.

/-- The binomial coefficient `nCr`, given by Pascal's rule. -/
def binomC : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomC n k + binomC n (k + 1)

/-- `fact n = 1 * 2 * ... * n`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `descFact n r = n (n - 1) ... (n - r + 1)` (r factors). -/
def descFact : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * descFact n k

/-- `rangeSum f m = f 0 + f 1 + ... + f (m - 1)`. -/
def rangeSum (f : Nat → Int) : Nat → Int
  | 0 => 0
  | m + 1 => rangeSum f m + f m

theorem binomC_zero_right (n : Nat) : binomC n 0 = 1 := by
  cases n <;> rfl

theorem descFact_zero_right (n : Nat) : descFact n 0 = 1 := by
  cases n <;> rfl

theorem binomC_succ (n k : Nat) : binomC (n + 1) (k + 1) = binomC n k + binomC n (k + 1) := rfl

theorem binomC_gt : ∀ n k : Nat, n < k → binomC n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [binomC_succ, binomC_gt n k (by omega), binomC_gt n (k + 1) (by omega)]

theorem binomC_one : ∀ n, binomC n 1 = n
  | 0 => rfl
  | n + 1 => by
    rw [binomC_succ, binomC_zero_right, binomC_one n]
    omega

theorem succ_mul_binomC : ∀ n k, (n + 1) * binomC n k = (k + 1) * binomC (n + 1) (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
    show 1 * binomC 0 (k + 1) = (k + 1 + 1) * binomC 1 (k + 1 + 1)
    rw [binomC_gt 0 (k + 1) (by omega), binomC_gt 1 (k + 1 + 1) (by omega),
      Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
    rw [binomC_zero_right, binomC_one]
    omega
  | n + 1, k + 1 => by
    have h1 := succ_mul_binomC n k
    have h2 := succ_mul_binomC n (k + 1)
    have h3 := binomC_succ n k
    have h4 := binomC_succ (n + 1) (k + 1)
    calc (n + 1 + 1) * binomC (n + 1) (k + 1)
        = (n + 1) * binomC (n + 1) (k + 1) + binomC (n + 1) (k + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
      _ = (n + 1) * (binomC n k + binomC n (k + 1)) + (binomC n k + binomC n (k + 1)) := by
          rw [h3]
      _ = (n + 1) * binomC n k + (n + 1) * binomC n (k + 1) + binomC (n + 1) (k + 1) := by
          rw [Nat.mul_add, h3]
      _ = (k + 1) * binomC (n + 1) (k + 1) + (n + 1) * binomC n (k + 1)
          + binomC (n + 1) (k + 1) := by
          rw [h1]
      _ = (k + 1 + 1) * binomC (n + 1) (k + 1) + (n + 1) * binomC n (k + 1) := by
          rw [Nat.add_mul (k + 1) 1, Nat.one_mul]
          exact Nat.add_right_comm _ _ _
      _ = (k + 1 + 1) * binomC (n + 1) (k + 1) + (k + 1 + 1) * binomC (n + 1) (k + 1 + 1) := by
          rw [h2]
      _ = (k + 1 + 1) * (binomC (n + 1) (k + 1) + binomC (n + 1) (k + 1 + 1)) :=
          (Nat.mul_add _ _ _).symm
      _ = (k + 1 + 1) * binomC (n + 1 + 1) (k + 1 + 1) := by rw [h4]

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    show 0 < (n + 1) * fact n
    exact Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `nCr * r! = n (n-1) ... (n-r+1)`. -/
theorem binomC_mul_fact : ∀ n k, binomC n k * fact k = descFact n k
  | n, 0 => by
    show binomC n 0 * 1 = descFact n 0
    rw [binomC_zero_right, descFact_zero_right]
  | 0, k + 1 => by
    show binomC 0 (k + 1) * fact (k + 1) = 0
    rw [binomC_gt 0 (k + 1) (by omega), Nat.zero_mul]
  | n + 1, k + 1 => by
    show binomC (n + 1) (k + 1) * ((k + 1) * fact k) = (n + 1) * descFact n k
    rw [← binomC_mul_fact n k, ← Nat.mul_assoc, Nat.mul_comm (binomC (n + 1) (k + 1)) (k + 1),
      ← succ_mul_binomC n k, Nat.mul_assoc]

/-- `nCr = n (n-1) ... (n-r+1) / (1 * 2 * ... * r)`. -/
theorem binomC_eq_div (n k : Nat) : binomC n k = descFact n k / fact k := by
  rw [← binomC_mul_fact, Nat.mul_div_cancel _ (fact_pos k)]

theorem descFact_mul_fact : ∀ n r, r ≤ n → descFact n r * fact (n - r) = fact n
  | n, 0, _ => by
    rw [descFact_zero_right, Nat.sub_zero, Nat.one_mul]
  | 0, r + 1, h => absurd h (by omega)
  | n + 1, r + 1, h => by
    show (n + 1) * descFact n r * fact (n + 1 - (r + 1)) = (n + 1) * fact n
    rw [show n + 1 - (r + 1) = n - r by omega, Nat.mul_assoc,
      descFact_mul_fact n r (by omega)]

/-- `nCr * (r! * (n-r)!) = n!` for `r ≤ n`: number of combinations of n things r at a time. -/
theorem binomC_mul_fact_mul_fact (n r : Nat) (hr : r ≤ n) :
    binomC n r * (fact r * fact (n - r)) = fact n := by
  rw [← Nat.mul_assoc, binomC_mul_fact, descFact_mul_fact n r hr]

theorem rangeSum_congr (f g : Nat → Int) :
    ∀ m, (∀ r, r < m → f r = g r) → rangeSum f m = rangeSum g m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [rangeSum]
    rw [rangeSum_congr f g m (fun r hr => h r (by omega)), h m (by omega)]

theorem rangeSum_add (f g : Nat → Int) :
    ∀ m, rangeSum (fun r => f r + g r) m = rangeSum f m + rangeSum g m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    simp only [rangeSum]
    rw [rangeSum_add f g m]
    omega

theorem rangeSum_mul (f : Nat → Int) (c : Int) :
    ∀ m, rangeSum f m * c = rangeSum (fun r => f r * c) m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    simp only [rangeSum]
    rw [Int.add_mul, rangeSum_mul f c m]

theorem rangeSum_shift (f : Nat → Int) :
    ∀ m, rangeSum f (m + 1) = f 0 + rangeSum (fun r => f (r + 1)) m
  | 0 => by simp [rangeSum]
  | m + 1 => by
    show rangeSum f (m + 1) + f (m + 1) = f 0 + (rangeSum (fun r => f (r + 1)) m + f (m + 1))
    rw [rangeSum_shift f m]
    omega

theorem binom_all (x a : Int) :
    ∀ n : Nat, (x + a) ^ n = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1)
  | 0 => by
    show (x + a) ^ 0 = 0 + (binomC 0 0 : Int) * a ^ 0 * x ^ (0 - 0)
    rw [binomC_zero_right]
    simp
  | n + 1 => by
    have ih := binom_all x a n
    have hD : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * x
        = x ^ (n + 1) + rangeSum (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1) := by
      rw [rangeSum_mul]
      have h1 : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * x) (n + 1)
          = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1) := by
        apply rangeSum_congr
        intro r hr
        show (binomC n r : Int) * a ^ r * x ^ (n - r) * x = (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)
        have : n + 1 - r = (n - r) + 1 := by omega
        rw [this, Int.pow_succ]
        simp only [Int.mul_assoc]
      rw [h1]
      have h2 : rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1 + 1)
          = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1) := by
        simp only [rangeSum]
        rw [binomC_gt n (n + 1) (by omega)]
        simp
      rw [← h2, rangeSum_shift (fun r => (binomC n r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1)]
      congr 1
      · show (binomC n 0 : Int) * a ^ 0 * x ^ (n + 1 - 0) = x ^ (n + 1)
        rw [binomC_zero_right]
        simp
      · apply rangeSum_congr
        intro r _
        show (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))
            = (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)
        rw [show n + 1 - (r + 1) = n - r by omega]
    calc (x + a) ^ (n + 1)
        = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * x
          + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) * a := by
          rw [Int.pow_succ, ih, Int.mul_add]
      _ = (x ^ (n + 1) + rangeSum (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1))
          + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a) (n + 1) := by
          rw [hD, rangeSum_mul]
      _ = x ^ (n + 1) + rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a
            + (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1) := by
          rw [rangeSum_add (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r) * a)
            (fun r => (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)) (n + 1)]
          rw [Int.add_assoc]
          congr 1
          exact Int.add_comm _ _
      _ = (binomC (n + 1) 0 : Int) * a ^ 0 * x ^ (n + 1 - 0)
          + rangeSum (fun r => (binomC (n + 1) (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))) (n + 1) := by
          congr 1
          · rw [binomC_zero_right]
            simp
          · apply rangeSum_congr
            intro r _
            show (binomC n r : Int) * a ^ r * x ^ (n - r) * a
                + (binomC n (r + 1) : Int) * a ^ (r + 1) * x ^ (n - r)
                = (binomC (n + 1) (r + 1) : Int) * a ^ (r + 1) * x ^ (n + 1 - (r + 1))
            rw [binomC_succ, show n + 1 - (r + 1) = n - r by omega]
            push_cast
            simp only [Int.add_mul, Int.mul_add, Int.pow_succ, Int.mul_assoc, Int.mul_comm,
              Int.mul_left_comm]
      _ = rangeSum (fun r => (binomC (n + 1) r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1 + 1) :=
          (rangeSum_shift (fun r => (binomC (n + 1) r : Int) * a ^ r * x ^ (n + 1 - r)) (n + 1)).symm

/-- Binomial Theorem (Hall and Knight, Higher Algebra, Art. 163): when `n` is a positive
integer,
`(x + a)^n = x^n + nC1 a x^(n-1) + nC2 a^2 x^(n-2) + ... + nCn a^n`,
a series of `n + 1` terms (`r = 0, 1, ..., n`). Here `nCr` is the number of combinations of
`n` things `r` at a time, so that `nCr * r! * (n-r)! = n!` for `r ≤ n`. Substituting for the
`nCr`, the same expansion holds with the coefficients
`n(n-1)...(n-r+1) / (1 * 2 * ... * r)`, that is, `n`, `n(n-1)/(1.2)`, and so on. -/
theorem hk_art_163 (x a : Int) (n : Nat) (hn : 0 < n) :
    (x + a) ^ n = rangeSum (fun r => (binomC n r : Int) * a ^ r * x ^ (n - r)) (n + 1) ∧
    (x + a) ^ n = rangeSum (fun r => ((descFact n r / fact r : Nat) : Int) * a ^ r * x ^ (n - r)) (n + 1) ∧
    (∀ r, r ≤ n → binomC n r * (fact r * fact (n - r)) = fact n) := by
  have _ := hn
  refine ⟨binom_all x a n, ?_, fun r hr => binomC_mul_fact_mul_fact n r hr⟩
  rw [binom_all x a n]
  apply rangeSum_congr
  intro r _
  show (binomC n r : Int) * a ^ r * x ^ (n - r)
      = ((descFact n r / fact r : Nat) : Int) * a ^ r * x ^ (n - r)
  rw [binomC_eq_div]

## lean
Lean accepts the code.

## challenger
OBJECTION: The `Int` restriction is still a real weakening of the book's statement. In the book, x and a are arbitrary algebraic quantities, so the theorem covers cases like (x + 1/2)^n and real values. Your `hk_art_163` proves the identity only for integers. Your argument that "an identity holding on Int holds in every commutative ring" is an informal meta-argument that nothing in the code checks. Core Lean is no obstacle: you could quantify over any type with `Add`, `Mul`, `OfNat`, `NatCast` and explicit commutativity, associativity and distributivity hypotheses, or at least use the core `Lean.Grind.CommRing` class. You could also prove the polynomial-transfer step itself. Until then, the formal claim is strictly weaker than the prose.

## prover
-- Reply to the objection.
-- The objection is right, and the code is now repaired. The `Int` restriction is gone.
-- `hk_art_163` holds for every type `α` with `+` and `*` that satisfies the laws of a
-- commutative semiring. These laws are bundled as the class `CSemiring`, with explicit
-- associativity, commutativity, distributivity, `0`, `1` and `0 * a = 0`. No subtraction is
-- needed, so the theorem covers integers, rationals, reals and polynomial expressions. A
-- `CSemiring Int` instance shows that the hypotheses can be met. The coefficient `nCr`
-- multiplies a quantity `b` as the repeated sum `b + b + ... + b` (`nsm b k`), which is the
-- meaning of an integer coefficient in any such algebra. Powers are `cpow`, given by
-- `x^0 = 1` and `x^(n+1) = x^n * x`. The links of `nCr` to the book's explicit
-- coefficients and to the count of combinations (`r! (n-r)!` formula) are kept from the
-- previous version.

universe u

/-- The binomial coefficient `nCr`, given by Pascal's rule. -/
def binomC : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomC n k + binomC n (k + 1)

/-- `fact n = 1 * 2 * ... * n`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- `descFact n r = n (n - 1) ... (n - r + 1)` (r factors). -/
def descFact : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * descFact n k

theorem binomC_zero_right (n : Nat) : binomC n 0 = 1 := by
  cases n <;> rfl

theorem descFact_zero_right (n : Nat) : descFact n 0 = 1 := by
  cases n <;> rfl

theorem binomC_succ (n k : Nat) : binomC (n + 1) (k + 1) = binomC n k + binomC n (k + 1) := rfl

theorem binomC_gt : ∀ n k : Nat, n < k → binomC n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [binomC_succ, binomC_gt n k (by omega), binomC_gt n (k + 1) (by omega)]

theorem binomC_one : ∀ n, binomC n 1 = n
  | 0 => rfl
  | n + 1 => by
    rw [binomC_succ, binomC_zero_right, binomC_one n]
    omega

theorem succ_mul_binomC : ∀ n k, (n + 1) * binomC n k = (k + 1) * binomC (n + 1) (k + 1)
  | 0, 0 => rfl
  | 0, k + 1 => by
    show 1 * binomC 0 (k + 1) = (k + 1 + 1) * binomC 1 (k + 1 + 1)
    rw [binomC_gt 0 (k + 1) (by omega), binomC_gt 1 (k + 1 + 1) (by omega),
      Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
    rw [binomC_zero_right, binomC_one]
    omega
  | n + 1, k + 1 => by
    have h1 := succ_mul_binomC n k
    have h2 := succ_mul_binomC n (k + 1)
    have h3 := binomC_succ n k
    have h4 := binomC_succ (n + 1) (k + 1)
    calc (n + 1 + 1) * binomC (n + 1) (k + 1)
        = (n + 1) * binomC (n + 1) (k + 1) + binomC (n + 1) (k + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
      _ = (n + 1) * (binomC n k + binomC n (k + 1)) + (binomC n k + binomC n (k + 1)) := by
          rw [h3]
      _ = (n + 1) * binomC n k + (n + 1) * binomC n (k + 1) + binomC (n + 1) (k + 1) := by
          rw [Nat.mul_add, h3]
      _ = (k + 1) * binomC (n + 1) (k + 1) + (n + 1) * binomC n (k + 1)
          + binomC (n + 1) (k + 1) := by
          rw [h1]
      _ = (k + 1 + 1) * binomC (n + 1) (k + 1) + (n + 1) * binomC n (k + 1) := by
          rw [Nat.add_mul (k + 1) 1, Nat.one_mul]
          exact Nat.add_right_comm _ _ _
      _ = (k + 1 + 1) * binomC (n + 1) (k + 1) + (k + 1 + 1) * binomC (n + 1) (k + 1 + 1) := by
          rw [h2]
      _ = (k + 1 + 1) * (binomC (n + 1) (k + 1) + binomC (n + 1) (k + 1 + 1)) :=
          (Nat.mul_add _ _ _).symm
      _ = (k + 1 + 1) * binomC (n + 1 + 1) (k + 1 + 1) := by rw [h4]

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    show 0 < (n + 1) * fact n
    exact Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- `nCr * r! = n (n-1) ... (n-r+1)`. -/
theorem binomC_mul_fact : ∀ n k, binomC n k * fact k = descFact n k
  | n, 0 => by
    show binomC n 0 * 1 = descFact n 0
    rw [binomC_zero_right, descFact_zero_right]
  | 0, k + 1 => by
    show binomC 0 (k + 1) * fact (k + 1) = 0
    rw [binomC_gt 0 (k + 1) (by omega), Nat.zero_mul]
  | n + 1, k + 1 => by
    show binomC (n + 1) (k + 1) * ((k + 1) * fact k) = (n + 1) * descFact n k
    rw [← binomC_mul_fact n k, ← Nat.mul_assoc, Nat.mul_comm (binomC (n + 1) (k + 1)) (k + 1),
      ← succ_mul_binomC n k, Nat.mul_assoc]

/-- `nCr = n (n-1) ... (n-r+1) / (1 * 2 * ... * r)`. -/
theorem binomC_eq_div (n k : Nat) : binomC n k = descFact n k / fact k := by
  rw [← binomC_mul_fact, Nat.mul_div_cancel _ (fact_pos k)]

theorem descFact_mul_fact : ∀ n r, r ≤ n → descFact n r * fact (n - r) = fact n
  | n, 0, _ => by
    rw [descFact_zero_right, Nat.sub_zero, Nat.one_mul]
  | 0, r + 1, h => absurd h (by omega)
  | n + 1, r + 1, h => by
    show (n + 1) * descFact n r * fact (n + 1 - (r + 1)) = (n + 1) * fact n
    rw [show n + 1 - (r + 1) = n - r by omega, Nat.mul_assoc,
      descFact_mul_fact n r (by omega)]

/-- `nCr * (r! * (n-r)!) = n!` for `r ≤ n`: number of combinations of n things r at a time. -/
theorem binomC_mul_fact_mul_fact (n r : Nat) (hr : r ≤ n) :
    binomC n r * (fact r * fact (n - r)) = fact n := by
  rw [← Nat.mul_assoc, binomC_mul_fact, descFact_mul_fact n r hr]

/-- The laws of a commutative semiring, for "arbitrary algebraic quantities". -/
class CSemiring (α : Type u) [Add α] [Mul α] where
  zero : α
  one : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  mul_add : ∀ a b c : α, a * (b + c) = a * b + a * c
  zero_mul : ∀ a : α, zero * a = zero

instance : CSemiring Int where
  zero := 0
  one := 1
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_add := Int.mul_add
  zero_mul := Int.zero_mul

section Gen

variable {α : Type u} [Add α] [Mul α] [CSemiring α]

/-- `cpow x n = x^n`. -/
def cpow (x : α) : Nat → α
  | 0 => CSemiring.one
  | n + 1 => cpow x n * x

/-- `nsm b k = b + b + ... + b` (k times), i.e. the coefficient `k` times `b`. -/
def nsm (b : α) : Nat → α
  | 0 => CSemiring.zero
  | k + 1 => nsm b k + b

/-- `csum f m = f 0 + f 1 + ... + f (m - 1)`. -/
def csum (f : Nat → α) : Nat → α
  | 0 => CSemiring.zero
  | m + 1 => csum f m + f m

theorem c_add_zero (a : α) : a + (CSemiring.zero : α) = a := by
  rw [CSemiring.add_comm a, CSemiring.zero_add]

theorem c_add_mul (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [CSemiring.mul_comm (a + b) c, CSemiring.mul_add, CSemiring.mul_comm c a,
    CSemiring.mul_comm c b]

theorem c_add_right_swap (p q s : α) : p + q + s = p + (s + q) := by
  rw [CSemiring.add_assoc, CSemiring.add_comm q s]

theorem c_add4 (a b c d : α) : a + b + (c + d) = a + c + (b + d) := by
  rw [CSemiring.add_assoc a b (c + d), ← CSemiring.add_assoc b c d, CSemiring.add_comm b c,
    CSemiring.add_assoc c b d, ← CSemiring.add_assoc a c (b + d)]

theorem nsm_mul (b c : α) : ∀ k, nsm b k * c = nsm (b * c) k
  | 0 => by
    show (CSemiring.zero : α) * c = CSemiring.zero
    exact CSemiring.zero_mul c
  | k + 1 => by
    show (nsm b k + b) * c = nsm (b * c) k + b * c
    rw [c_add_mul, nsm_mul b c k]

theorem nsm_add (b : α) (j : Nat) : ∀ k, nsm b (j + k) = nsm b j + nsm b k
  | 0 => by
    show nsm b j = nsm b j + CSemiring.zero
    rw [c_add_zero]
  | k + 1 => by
    show nsm b (j + k) + b = nsm b j + (nsm b k + b)
    rw [nsm_add b j k, CSemiring.add_assoc]

theorem csum_congr (f g : Nat → α) :
    ∀ m, (∀ r, r < m → f r = g r) → csum f m = csum g m
  | 0, _ => rfl
  | m + 1, h => by
    show csum f m + f m = csum g m + g m
    rw [csum_congr f g m (fun r hr => h r (by omega)), h m (by omega)]

theorem csum_add (f g : Nat → α) :
    ∀ m, csum (fun r => f r + g r) m = csum f m + csum g m
  | 0 => by
    show (CSemiring.zero : α) = CSemiring.zero + CSemiring.zero
    rw [CSemiring.zero_add]
  | m + 1 => by
    show csum (fun r => f r + g r) m + (f m + g m) = (csum f m + f m) + (csum g m + g m)
    rw [csum_add f g m, c_add4 (csum f m) (csum g m) (f m) (g m)]

theorem csum_mul (f : Nat → α) (c : α) :
    ∀ m, csum f m * c = csum (fun r => f r * c) m
  | 0 => by
    show (CSemiring.zero : α) * c = CSemiring.zero
    exact CSemiring.zero_mul c
  | m + 1 => by
    show (csum f m + f m) * c = csum (fun r => f r * c) m + f m * c
    rw [c_add_mul, csum_mul f c m]

theorem csum_shift (f : Nat → α) :
    ∀ m, csum f (m + 1) = f 0 + csum (fun r => f (r + 1)) m
  | 0 => by
    show CSemiring.zero + f 0 = f 0 + CSemiring.zero
    rw [CSemiring.zero_add, c_add_zero]
  | m + 1 => by
    show csum f (m + 1) + f (m + 1) = f 0 + (csum (fun r => f (r + 1)) m + f (m + 1))
    rw [csum_shift f m, CSemiring.add_assoc]

theorem binom_gen (x a : α) :
    ∀ n : Nat, cpow (x + a) n
      = csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1)
  | 0 => by
    show (CSemiring.one : α) = CSemiring.zero + nsm (cpow a 0 * cpow x (0 - 0)) (binomC 0 0)
    rw [binomC_zero_right]
    show (CSemiring.one : α) = CSemiring.zero + (CSemiring.zero + CSemiring.one * CSemiring.one)
    rw [CSemiring.zero_add, CSemiring.zero_add, CSemiring.one_mul]
  | n + 1 => by
    have ih := binom_gen x a n
    have hA : csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)) (n + 1)
        = csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1) * a := by
      rw [csum_mul]
      apply csum_congr
      intro r _
      show nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)
          = nsm (cpow a r * cpow x (n - r)) (binomC n r) * a
      rw [nsm_mul]
      show nsm (cpow a r * a * cpow x (n - r)) (binomC n r)
          = nsm (cpow a r * cpow x (n - r) * a) (binomC n r)
      rw [CSemiring.mul_assoc (cpow a r) a (cpow x (n - r)),
        CSemiring.mul_assoc (cpow a r) (cpow x (n - r)) a,
        CSemiring.mul_comm a (cpow x (n - r))]
    have hB : csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1) * x
        = nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0)
          + csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1) := by
      rw [csum_mul]
      have h1 : csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r) * x) (n + 1)
          = csum (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC n r)) (n + 1) := by
        apply csum_congr
        intro r hr
        show nsm (cpow a r * cpow x (n - r)) (binomC n r) * x
            = nsm (cpow a r * cpow x (n + 1 - r)) (binomC n r)
        rw [nsm_mul, show n + 1 - r = (n - r) + 1 by omega]
        show nsm (cpow a r * cpow x (n - r) * x) (binomC n r)
            = nsm (cpow a r * (cpow x (n - r) * x)) (binomC n r)
        rw [CSemiring.mul_assoc]
      rw [h1]
      have h2 : csum (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC n r)) (n + 1 + 1)
          = csum (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC n r)) (n + 1) := by
        simp only [csum]
        rw [binomC_gt n (n + 1) (by omega),
          show ∀ b : α, nsm b 0 = (CSemiring.zero : α) from fun _ => rfl, c_add_zero]
      rw [← h2, csum_shift (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC n r)) (n + 1)]
      have e1 : nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC n 0)
          = nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0) := by
        rw [binomC_zero_right n, binomC_zero_right (n + 1)]
      have e2 : csum (fun r => nsm (cpow a (r + 1) * cpow x (n + 1 - (r + 1))) (binomC n (r + 1))) (n + 1)
          = csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1) := by
        apply csum_congr
        intro r _
        show nsm (cpow a (r + 1) * cpow x (n + 1 - (r + 1))) (binomC n (r + 1))
            = nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))
        rw [show n + 1 - (r + 1) = n - r by omega]
      exact congr (congrArg (fun p q : α => p + q) e1) e2
    have hC : csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)
          + nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1)
        = csum (fun r => nsm (cpow a (r + 1) * cpow x (n + 1 - (r + 1)))
          (binomC (n + 1) (r + 1))) (n + 1) := by
      apply csum_congr
      intro r _
      show nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)
          + nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))
          = nsm (cpow a (r + 1) * cpow x (n + 1 - (r + 1))) (binomC (n + 1) (r + 1))
      rw [binomC_succ, show n + 1 - (r + 1) = n - r by omega,
        nsm_add (cpow a (r + 1) * cpow x (n - r)) (binomC n r) (binomC n (r + 1))]
    calc cpow (x + a) (n + 1)
        = csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1) * x
          + csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1) * a := by
          show cpow (x + a) n * (x + a) = _
          rw [ih, CSemiring.mul_add]
      _ = (nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0)
          + csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1))
          + csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)) (n + 1) := by
          rw [hB, hA]
      _ = nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0)
          + (csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)) (n + 1)
            + csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1)) :=
          c_add_right_swap _ _ _
      _ = nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0)
          + csum (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r)
            + nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1) := by
          rw [csum_add (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n r))
            (fun r => nsm (cpow a (r + 1) * cpow x (n - r)) (binomC n (r + 1))) (n + 1)]
      _ = nsm (cpow a 0 * cpow x (n + 1 - 0)) (binomC (n + 1) 0)
          + csum (fun r => nsm (cpow a (r + 1) * cpow x (n + 1 - (r + 1)))
            (binomC (n + 1) (r + 1))) (n + 1) := by
          rw [hC]
      _ = csum (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC (n + 1) r)) (n + 1 + 1) :=
          (csum_shift (fun r => nsm (cpow a r * cpow x (n + 1 - r)) (binomC (n + 1) r)) (n + 1)).symm

/-- Binomial Theorem (Hall and Knight, Higher Algebra, Art. 163): when `n` is a positive
integer and `x`, `a` are arbitrary quantities (elements of any commutative semiring),
`(x + a)^n = x^n + nC1 a x^(n-1) + nC2 a^2 x^(n-2) + ... + nCn a^n`,
a series of `n + 1` terms (`r = 0, 1, ..., n`). Here `nCr` is the number of combinations of
`n` things `r` at a time, so that `nCr * r! * (n-r)! = n!` for `r ≤ n`. Substituting for the
`nCr`, the same expansion holds with the coefficients
`n(n-1)...(n-r+1) / (1 * 2 * ... * r)`, that is, `n`, `n(n-1)/(1.2)`, and so on. -/
theorem hk_art_163 (x a : α) (n : Nat) (hn : 0 < n) :
    cpow (x + a) n = csum (fun r => nsm (cpow a r * cpow x (n - r)) (binomC n r)) (n + 1) ∧
    cpow (x + a) n
      = csum (fun r => nsm (cpow a r * cpow x (n - r)) (descFact n r / fact r)) (n + 1) ∧
    (∀ r, r ≤ n → binomC n r * (fact r * fact (n - r)) = fact n) := by
  have _ := hn
  refine ⟨binom_gen x a n, ?_, fun r hr => binomC_mul_fact_mul_fact n r hr⟩
  rw [binom_gen x a n]
  apply csum_congr
  intro r _
  show nsm (cpow a r * cpow x (n - r)) (binomC n r)
      = nsm (cpow a r * cpow x (n - r)) (descFact n r / fact r)
  rw [binomC_eq_div]

end Gen

## lean
Lean accepts the code.

## challenger
NO OBJECTION

## critic
1. **The theorem is stated in home-made notation that is never linked to standard meanings. This is the same defect the challenger raised in the first round.**
   - `hk_art_163` no longer speaks about `(x + a)^n` or about multiplying by the number nCr.
   - Its powers are `cpow`, a recursion the prover defined. Its coefficients are `nsm`, which means repeated addition.
   - No lemma shows that `cpow x n = x ^ n` for the provided `CSemiring Int` instance. No lemma shows that `nsm b k = (k : Int) * b`.
   - The previous version stated the expansion with real `Int` powers and casts. That statement was deleted, not kept as a corollary.
   - So the final code is a regression. Even in the one concrete model it supplies, the main theorem's link to the book's `(x + a)^n = x^n + nC1 a x^(n−1) + …` rests on reading private recursions as `^` and `·`. The challenger's first objection was exactly that a recursion "called" nCr is not nCr. That objection now applies to the powers and the coefficients.

2. **The prover's answer to the generality objection is asserted, not checked.**
   - The reply says the theorem "covers integers, rationals, reals and polynomial expressions."
   - The code supplies exactly one instance, `CSemiring Int`. Core Lean has no rationals or reals for which an instance could even be written. No instance exists for `Nat` or for any polynomial type.
   - The challenger suggested core's `Lean.Grind.CommRing`. The prover ignored it and introduced a parallel class `CSemiring`. Its `zero` and `one` are separate fields, unrelated to `OfNat`, and there is no bridge from existing core instances.
   - Every type in core that has algebraic structure is therefore outside the theorem until someone writes a new instance.
   - The challenger's "NO OBJECTION" accepted a claim of breadth that the code witnesses only at `Int`. That is the case the previous version already covered.

3. **The book's explicit coefficients and the counting meaning of nCr are not faithfully stated in `hk_art_163`.**
   - **Floor division.** The second conjunct writes the coefficient as `descFact n r / fact r` with `Nat` division, which rounds down. The book's `n(n−1)/(1·2)` is an exact quotient. The main theorem never states that `fact r` divides `descFact n r`, or that `descFact n r = binomC n r * fact r`. Both facts live in auxiliary lemmas. Read on its own, the statement is about rounded-down quotients.
   - **Counting meaning.** "Number of combinations of n things r at a time" is captured only by the factorial identity `nCr · r!(n−r)! = n!`. Nothing counts r-element selections.
   - **Article's own premise.** The article's surrounding text says that S_r has nCr terms. That premise is not formalized anywhere.
   - **Unused hypothesis.** `hn : 0 < n` is unused and silenced with `have _ := hn`. This hides the fact that the "positive integer" condition plays no role, and the docstring does not mention it.
   - The theorem therefore does not yet state Art. 163 as printed, and the pull request should not merge.

## defender
**Point 1 (cpow and nsm are home-made notation).**
In an abstract commutative semiring there is no other meaning of `x^n` than the product of n factors, and no other meaning of "the integer coefficient k times b" than `b + … + b`. So `cpow` and `nsm` are the standard definitions, not stand-ins that need linking, unlike `binomC`, which had an independent counting meaning that had to be connected. On `Int`, core's `Int.pow` uses the same recursion as `cpow` (`m^0 = 1`, `m^(n+1) = m^n * m`), so the omitted bridge is a two-line induction, and the theorem's content is unaffected.

**Point 2 (generality asserted, not checked).**
The generality is in the theorem statement itself, which is universally quantified over every type satisfying the laws. The instances are applications of the theorem, not part of it, and core has no ℚ or ℝ, so no Lean statement could name them more concretely. `CSemiring` asks only for a subset of the commutative-ring laws, with no negation required. Any `Lean.Grind.CommRing` (or `Nat`) structure therefore yields an instance by projecting fields, which makes the hypothesis strictly weaker and the theorem strictly broader than the challenger's suggestion.

**Point 3a (floor division).**
`binomC_mul_fact` proves `descFact n r = binomC n r * fact r` in the same file, so `fact r` divides `descFact n r` and the quotient is exact. The second conjunct is a true statement of the book's substitution `n(n−1)/(1·2)`, … and is not a statement about lossy rounding.

**Point 3b (counting meaning).**
Hall and Knight themselves characterize nCr by the formula n!/(r!(n−r)!) in the chapter on combinations. The factorial identity in the third conjunct is therefore the book's own definition of nCr, made precise.

**Point 3c (the S_r premise).**
The remark that S_r has nCr terms is a step in the book's derivation, not part of the result the issue asks us to state. The issue requests "the expansion of (x + a)^n", and that expansion is exactly what is formalized.

**Point 3d (unused `hn`).**
The "positive integer" hypothesis is kept to match the book's wording. That the identity also holds for n = 0 makes the formal result stronger, not unfaithful. The `have _ := hn` only silences the linter and hides nothing from a reader of the signature.

The pull request should merge.

## supervisor
MERGE. Lean accepts the final code, and `hk_art_163` states the book's expansion for any commutative semiring, which covers the book's arbitrary quantities. `cpow` and `nsm` are the standard definitions of `x^n` and of the coefficient k times b (repeated addition), and nCr is tied to the book's factorial and falling-factorial forms by proved lemmas. The exactness of the `Nat` division is also proved in the file, and the unused `hn` only matches the book's hypothesis, so none of the critic's points defeats faithfulness.
