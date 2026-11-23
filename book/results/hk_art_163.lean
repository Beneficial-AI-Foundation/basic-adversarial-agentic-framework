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
