-- The challenger's objection is accepted and the code is repaired.
-- * A uniqueness lemma `isLog_unique` is added. If `IsLog a F e` and `IsLog a F e'` hold, with
--   a ≠ 1 and F positive, then e and e' are the same rational. In Nat-safe form this reads
--   (e.1 − e.2.1)·e'.2.2 = (e'.1 − e'.2.1)·e.2.2, and `ERel` states it.
--   Its proof uses the hypothesis a₁ ≠ a₂, so that hypothesis now does real work.
-- * `hk_art_205` now states the book's equation of values. Under the hypotheses, x − y is a
--   logarithm of M/N, and every logarithm of M/N equals x − y as a rational.
--   So log_a (M/N) = log_a M − log_a N.
-- Scope, unchanged from the last version:
-- * The base is a positive rational a = a₁/a₂ with a ≠ 1.
-- * M and N are positive rationals, compared by cross-multiplication.
-- * Exponents are arbitrary rationals. The triple (p, n, d) with d > 0 stands for (p − n)/d.
-- * Irrational exponents and real bases remain out of scope, because the Lean core library
--   has no real numbers.

/-- Art. 199: the rational exponent `e = (e.1 - e.2.1) / e.2.2` is a logarithm of the
fraction `F = F.1 / F.2` to the base `a = a.1 / a.2` when `a ^ e = F`, that is
`(a.1/a.2)^(e.1 - e.2.1) = (F.1/F.2)^(e.2.2)`, stated by cross-multiplication. -/
def IsLog (a F : Nat × Nat) (e : Nat × Nat × Nat) : Prop :=
  a.1 ^ e.1 * a.2 ^ e.2.1 * F.2 ^ e.2.2 = a.2 ^ e.1 * a.1 ^ e.2.1 * F.1 ^ e.2.2

/-- The rational exponents `e` and `e'` are equal:
`(e.1 - e.2.1) * e'.2.2 = (e'.1 - e'.2.1) * e.2.2`, written without subtraction. -/
def ERel (e e' : Nat × Nat × Nat) : Prop :=
  e.1 * e'.2.2 + e'.2.1 * e.2.2 = e'.1 * e.2.2 + e.2.1 * e'.2.2

/-- Quotient of the fractions `M = M.1 / M.2` and `N = N.1 / N.2`. -/
def fdiv (M N : Nat × Nat) : Nat × Nat := (M.1 * N.2, M.2 * N.1)

/-- Difference of the rational exponents `x = (r₁ - r₂)/s` and `y = (t₁ - t₂)/u`,
namely `((r₁u + t₂s) - (r₂u + t₁s)) / (su)`. -/
def esub (x y : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (x.1 * y.2.2 + y.2.1 * x.2.2, x.2.1 * y.2.2 + y.1 * x.2.2, x.2.2 * y.2.2)

/-- Strict monotonicity of positive powers. -/
theorem hk_pow_lt {a b : Nat} (h : a < b) : ∀ m, 0 < m → a ^ m < b ^ m
  | 0, hm => absurd hm (Nat.lt_irrefl 0)
  | k + 1, _ => by
    have h1 : a ^ k ≤ b ^ k := Nat.pow_le_pow_left (Nat.le_of_lt h) k
    have h2 : 0 < b ^ k := Nat.pow_pos (Nat.lt_of_le_of_lt (Nat.zero_le a) h)
    have h3 : a ^ k * a ≤ b ^ k * a := Nat.mul_le_mul h1 (Nat.le_refl a)
    have h4 : b ^ k * (a + 1) ≤ b ^ k * b := Nat.mul_le_mul (Nat.le_refl _) h
    have h5 : b ^ k * (a + 1) = b ^ k * a + b ^ k := Nat.mul_succ _ _
    have h6 : b ^ k * a < b ^ k * (a + 1) := by rw [h5]; omega
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.lt_of_le_of_lt h3 (Nat.lt_of_lt_of_le h6 h4)

theorem hk_pow_cancel_aux (a₁ a₂ K j : Nat) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hne : a₁ ≠ a₂)
    (hj : 0 < j) (h : a₁ ^ K * a₂ ^ (K + j) = a₁ ^ (K + j) * a₂ ^ K) : False := by
  have hC : 0 < a₁ ^ K * a₂ ^ K := Nat.mul_pos (Nat.pow_pos h₁) (Nat.pow_pos h₂)
  have h' : a₁ ^ K * a₂ ^ K * a₂ ^ j = a₁ ^ K * a₂ ^ K * a₁ ^ j := by
    calc a₁ ^ K * a₂ ^ K * a₂ ^ j = a₁ ^ K * a₂ ^ (K + j) := by rw [Nat.pow_add]; ac_rfl
      _ = a₁ ^ (K + j) * a₂ ^ K := h
      _ = a₁ ^ K * a₂ ^ K * a₁ ^ j := by rw [Nat.pow_add]; ac_rfl
  have hj' : a₂ ^ j = a₁ ^ j := Nat.eq_of_mul_eq_mul_left hC h'
  rcases Nat.lt_or_ge a₁ a₂ with hlt | hge
  · have := hk_pow_lt hlt j hj
    rw [hj'] at this
    exact Nat.lt_irrefl _ this
  · have hgt : a₂ < a₁ := by omega
    have := hk_pow_lt hgt j hj
    rw [hj'] at this
    exact Nat.lt_irrefl _ this

theorem hk_pow_cancel (a₁ a₂ K L : Nat) (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hne : a₁ ≠ a₂)
    (h : a₁ ^ K * a₂ ^ L = a₁ ^ L * a₂ ^ K) : K = L := by
  by_cases hKL : K = L
  · exact hKL
  · exfalso
    rcases Nat.lt_or_ge K L with hlt | hge
    · obtain ⟨j, hj⟩ : ∃ j, L = K + j := ⟨L - K, by omega⟩
      subst hj
      exact hk_pow_cancel_aux a₁ a₂ K j h₁ h₂ hne (by omega) h
    · have hgt : L < K := by omega
      obtain ⟨j, hj⟩ : ∃ j, K = L + j := ⟨K - L, by omega⟩
      subst hj
      exact hk_pow_cancel_aux a₂ a₁ L j h₂ h₁ (Ne.symm hne) (by omega) (by
        calc a₂ ^ L * a₁ ^ (L + j) = a₁ ^ (L + j) * a₂ ^ L := Nat.mul_comm _ _
          _ = a₁ ^ L * a₂ ^ (L + j) := h
          _ = a₂ ^ (L + j) * a₁ ^ L := Nat.mul_comm _ _)

/-- Uniqueness of the logarithm (Art. 199): for a positive base `a ≠ 1` and a positive
fraction `F`, any two logarithms of `F` to the base `a` are the same rational number. -/
theorem isLog_unique (a F : Nat × Nat) (e e' : Nat × Nat × Nat)
    (ha₁ : 0 < a.1) (ha₂ : 0 < a.2) (ha : a.1 ≠ a.2) (hF₁ : 0 < F.1) (hF₂ : 0 < F.2)
    (h : IsLog a F e) (h' : IsLog a F e') : ERel e e' := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨f₁, f₂⟩ := F
  obtain ⟨p, n, d⟩ := e
  obtain ⟨p', n', d'⟩ := e'
  dsimp only [IsLog, ERel] at *
  have e1 := congrArg (· ^ d') h
  have e2 := congrArg (· ^ d) h'
  simp only [Nat.mul_pow, ← Nat.pow_mul] at e1 e2
  rw [Nat.mul_comm d' d] at e2
  have hK : a₁ ^ (p * d' + n' * d) * a₂ ^ (n * d' + p' * d)
      = a₁ ^ (n * d' + p' * d) * a₂ ^ (p * d' + n' * d) := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos (Nat.pow_pos hF₂ : 0 < f₂ ^ (d * d')) (Nat.pow_pos hF₁ : 0 < f₁ ^ (d * d')))
    calc f₂ ^ (d * d') * f₁ ^ (d * d') * (a₁ ^ (p * d' + n' * d) * a₂ ^ (n * d' + p' * d))
        = (a₁ ^ (p * d') * a₂ ^ (n * d') * f₂ ^ (d * d'))
            * (a₂ ^ (p' * d) * a₁ ^ (n' * d) * f₁ ^ (d * d')) := by
          simp only [Nat.pow_add]; ac_rfl
      _ = (a₂ ^ (p * d') * a₁ ^ (n * d') * f₁ ^ (d * d'))
            * (a₁ ^ (p' * d) * a₂ ^ (n' * d) * f₂ ^ (d * d')) := by
          rw [e1, e2]
      _ = f₂ ^ (d * d') * f₁ ^ (d * d') * (a₁ ^ (n * d' + p' * d) * a₂ ^ (p * d' + n' * d)) := by
          simp only [Nat.pow_add]; ac_rfl
  have hKL := hk_pow_cancel a₁ a₂ _ _ ha₁ ha₂ ha hK
  exact hKL.trans (Nat.add_comm _ _)

/-- Existence part: `x - y` is a logarithm of `M / N`. -/
theorem isLog_sub (a₁ a₂ m₁ m₂ n₁ n₂ r₁ r₂ s t₁ t₂ u : Nat)
    (hx : IsLog (a₁, a₂) (m₁, m₂) (r₁, r₂, s))
    (hy : IsLog (a₁, a₂) (n₁, n₂) (t₁, t₂, u)) :
    IsLog (a₁, a₂) (fdiv (m₁, m₂) (n₁, n₂)) (esub (r₁, r₂, s) (t₁, t₂, u)) := by
  dsimp only [IsLog, fdiv, esub] at *
  have hxu := congrArg (· ^ u) hx
  have hyu := congrArg (· ^ s) hy
  simp only [Nat.mul_pow, ← Nat.pow_mul] at hxu hyu
  rw [Nat.mul_comm u s] at hyu
  calc a₁ ^ (r₁ * u + t₂ * s) * a₂ ^ (r₂ * u + t₁ * s) * (m₂ * n₁) ^ (s * u)
      = (a₁ ^ (r₁ * u) * a₂ ^ (r₂ * u) * m₂ ^ (s * u))
          * (a₂ ^ (t₁ * s) * a₁ ^ (t₂ * s) * n₁ ^ (s * u)) := by
        simp only [Nat.pow_add, Nat.mul_pow]; ac_rfl
    _ = (a₂ ^ (r₁ * u) * a₁ ^ (r₂ * u) * m₁ ^ (s * u))
          * (a₁ ^ (t₁ * s) * a₂ ^ (t₂ * s) * n₂ ^ (s * u)) := by
        rw [hxu, ← hyu]
    _ = a₂ ^ (r₁ * u + t₂ * s) * a₁ ^ (r₂ * u + t₁ * s) * (m₁ * n₂) ^ (s * u) := by
        simp only [Nat.pow_add, Nat.mul_pow]; ac_rfl

/-- Art. 205. Let `a = a₁/a₂ ≠ 1` be a positive rational base. Let `M = m₁/m₂` and
`N = n₁/n₂` be positive fractions. Suppose `x = log_a M` and `y = log_a N` are rational
exponents, that is `a ^ x = M` and `a ^ y = N`. Then `x - y` is a logarithm of `M / N`,
and every logarithm of `M / N` equals `x - y` as a rational. That is,
`log_a (M / N) = x - y = log_a M - log_a N`. -/
theorem hk_art_205 (a₁ a₂ m₁ m₂ n₁ n₂ r₁ r₂ s t₁ t₂ u : Nat)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha : a₁ ≠ a₂)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (_hs : 0 < s) (_hu : 0 < u)
    (hx : IsLog (a₁, a₂) (m₁, m₂) (r₁, r₂, s))
    (hy : IsLog (a₁, a₂) (n₁, n₂) (t₁, t₂, u)) :
    IsLog (a₁, a₂) (fdiv (m₁, m₂) (n₁, n₂)) (esub (r₁, r₂, s) (t₁, t₂, u)) ∧
    ∀ z : Nat × Nat × Nat, IsLog (a₁, a₂) (fdiv (m₁, m₂) (n₁, n₂)) z →
      ERel z (esub (r₁, r₂, s) (t₁, t₂, u)) := by
  have hex := isLog_sub a₁ a₂ m₁ m₂ n₁ n₂ r₁ r₂ s t₁ t₂ u hx hy
  refine ⟨hex, fun z hz => ?_⟩
  exact isLog_unique (a₁, a₂) (fdiv (m₁, m₂) (n₁, n₂)) z _ ha₁ ha₂ ha
    (Nat.mul_pos hm₁ hn₂) (Nat.mul_pos hm₂ hn₁) hz hex
