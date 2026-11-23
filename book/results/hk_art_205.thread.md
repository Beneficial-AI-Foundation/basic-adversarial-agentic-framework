## issue
Issue #205. To find the logarithm of a fraction (Art. 205)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XVI (Logarithms), Art. 205.
The book prints the following text.
199. DEFINITION. The logarithm of any number to a given base is the index of the power to which the base must be raised in order to equal the given number. Thus if a^x = N, x is called the logarithm of N to the base a.
Let M/N be the fraction, and suppose x = log_a M, y = log_a N; so that a^x = M, a^y = N.
log_a (M/N) = x − y = log_a M − log_a N.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_205.

## prover
-- Scope of this formalisation. The Lean core library has no real numbers and no real
-- logarithm. So the logarithm is modelled by the book's own definition (Art. 199) as a
-- relation: x is a logarithm of N to the base a when a ^ x = N.
-- The statement is limited to natural numbers. The base a, the numbers M and N and the
-- exponents x and y are all natural numbers.
-- The hypothesis y ≤ x is added so that the fraction M / N is a whole number. Then Nat
-- subtraction and Nat division are exact.
-- The book's claim for real numbers and real exponents is not proved here.

/-- Art. 199: `x` is the logarithm of `N` to the base `a` when `a ^ x = N`. -/
def IsLog (a N x : Nat) : Prop := a ^ x = N

/-- Art. 205 (case of natural numbers). Suppose `x = log_a M` and `y = log_a N`,
so that `a ^ x = M` and `a ^ y = N`. If `y ≤ x`, then `x - y` is a logarithm of
the fraction `M / N` to the base `a`. That is, `log_a (M / N) = log_a M - log_a N`. -/
theorem hk_art_205 (a M N x y : Nat) (ha : 0 < a)
    (hx : IsLog a M x) (hy : IsLog a N y) (hxy : y ≤ x) :
    IsLog a (M / N) (x - y) := by
  unfold IsLog at *
  subst hx
  subst hy
  have h : a ^ x = a ^ (x - y) * a ^ y := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hxy]
  rw [h, Nat.mul_div_cancel _ (Nat.pow_pos ha)]

## lean
Lean accepts the code.

## challenger
OBJECTION: The hypothesis `y ≤ x` plus Nat division means `M / N` is always a whole number. So the theorem never covers an actual fraction: neither the case M < N, where the logarithm x − y is negative, nor any non-integral quotient. What is proved is only the index law a^x / a^y = a^(x−y), a strictly weaker special case of Art. 205. The book's case can be stated faithfully in core Lean, with integer exponents and the fraction M/N encoded as a pair of naturals compared by cross-multiplication (for example `IsLog a (p, q) z` meaning a^z·q = p for z ≥ 0 and p·a^(−z) = q otherwise), so the restriction is not forced by the missing real numbers.

## prover
-- The objection is accepted and the code is repaired.
-- Exponents are now integers, so a negative logarithm (the case M < N) is covered.
-- A fraction is a pair (p, q) of naturals standing for p / q. Fractions are compared
-- by cross-multiplication, so non-integral quotients such as 2/3 are covered.
-- `IsLog a (p, q) z` says that a ^ z = p / q, written without division as
--   p * a ^ (-z).toNat = q * a ^ z.toNat.
-- For z ≥ 0 this reads p = q * a ^ z. For z < 0 it reads p * a ^ (-z) = q.
-- The quotient of the fractions M = m₁/m₂ and N = n₁/n₂ is (m₁ * n₂) / (m₂ * n₁).
-- The base and the fractions are still positive rational, not real. Real exponents
-- remain out of scope, because the Lean core library has no real numbers.

/-- Art. 199: the integer `z` is a logarithm of the fraction `F = F.1 / F.2` to the base `a`
when `a ^ z = F.1 / F.2`, stated by cross-multiplication. -/
def IsLog (a : Nat) (F : Nat × Nat) (z : Int) : Prop :=
  F.1 * a ^ (-z).toNat = F.2 * a ^ z.toNat

/-- Quotient of the fractions `M = M.1 / M.2` and `N = N.1 / N.2`. -/
def fdiv (M N : Nat × Nat) : Nat × Nat := (M.1 * N.2, M.2 * N.1)

/-- Art. 205. Let `M = m₁/m₂` and `N = n₁/n₂` be positive fractions and `a > 0` the base.
If `x = log_a M` and `y = log_a N`, that is `a ^ x = M` and `a ^ y = N`, then
`log_a (M / N) = x - y = log_a M - log_a N`. -/
theorem hk_art_205 (a m₁ m₂ n₁ n₂ : Nat) (x y : Int) (ha : 0 < a)
    (_hm₂ : 0 < m₂) (_hn₁ : 0 < n₁) (_hn₂ : 0 < n₂)
    (hx : IsLog a (m₁, m₂) x) (hy : IsLog a (n₁, n₂) y) :
    IsLog a (fdiv (m₁, m₂) (n₁, n₂)) (x - y) := by
  dsimp only [IsLog, fdiv] at *
  have hexp : (-(x - y)).toNat + x.toNat + (-y).toNat
      = (x - y).toNat + (-x).toNat + y.toNat := by omega
  apply Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Nat.pow_pos ha : 0 < a ^ (-x).toNat) (Nat.pow_pos ha : 0 < a ^ y.toNat))
  calc m₁ * n₂ * a ^ (-(x - y)).toNat * (a ^ (-x).toNat * a ^ y.toNat)
      = (m₁ * a ^ (-x).toNat) * (n₂ * a ^ y.toNat) * a ^ (-(x - y)).toNat := by ac_rfl
    _ = (m₂ * a ^ x.toNat) * (n₁ * a ^ (-y).toNat) * a ^ (-(x - y)).toNat := by
        rw [hx, ← hy]
    _ = m₂ * n₁ * a ^ ((-(x - y)).toNat + x.toNat + (-y).toNat) := by
        rw [Nat.pow_add, Nat.pow_add]; ac_rfl
    _ = m₂ * n₁ * a ^ ((x - y).toNat + (-x).toNat + y.toNat) := by rw [hexp]
    _ = m₂ * n₁ * a ^ (x - y).toNat * (a ^ (-x).toNat * a ^ y.toNat) := by
        rw [Nat.pow_add, Nat.pow_add]; ac_rfl

## lean
Lean accepts the code.

## challenger
NO OBJECTION

## critic
**Against merging hk_art_205: three objections**

1. **The theorem is empty for almost every fraction the article covers.** Art. 205 applies to any positive M and N, using the logarithm defined in Art. 199. The final code only allows logarithms that are integers and bases that are natural numbers. So the hypotheses `hx` and `hy` can only be met when M and N are exact integer powers of a. Take a = 10 and M = 2: no integer x satisfies `IsLog 10 (2, 1) x`, so the theorem says nothing about log₁₀ 2. That is exactly the kind of value the logarithm chapter is about. The challenger argued that the earlier restriction was "not forced by the missing real numbers." The same argument applies here. Rational exponents can be stated in core Lean without reals: a^(r/s) = p/q can be written as a^r · q^s = p^s by cross-multiplication. Rational bases, such as base 1/2, are also excluded, and they too could be stated. The prover accepted the challenger's specific encoding but not the principle behind it. Integer exponents are still a special case of Art. 205, much like the first version.

2. **The book's equation is formalised only as a relation, and uniqueness is not settled.** The article asserts an equality of values: log_a(M/N) = log_a M − log_a N. `IsLog` is a relation, and the theorem only shows that x − y is *a* logarithm of the quotient. It never shows that it is *the* logarithm.
   - The hypothesis `ha : 0 < a` allows a = 1.
   - For a = 1, `IsLog 1 (p, q) z` holds for every integer z whenever p = q.
   - So "log₁ M" has no single value, and the theorem's reading as "log_a(M/N) = log_a M − log_a N" fails in that case.
   
   A faithful statement needs `1 < a` (or a ≠ 1), plus a uniqueness lemma, so that the relation actually defines the function the book writes. Neither is present.

3. **The documentation misstates what was proved, and the accepted fix was not checked against the issue.** The repair's comments say "The base and the fractions are still positive rational." In the code, however, the base `a` is a `Nat`, so a rational base is not covered. The comments also say only "real exponents" remain out of scope. That hides the fact that rational exponents, and so every non-trivial logarithm, are also out of scope. The challenger's "NO OBJECTION" only confirms that its own proposed encoding was adopted. It does not show that the code matches the prose of Art. 205. A reader who trusts the header will overestimate what this theorem proves.

## defender
**Defender's rebuttal: hk_art_205 should merge**

1. **Integer exponents.** The critic's own example defeats the critic's proposed fix. log₁₀ 2 is irrational, so no rational-exponent encoding such as a^r·q^s = p^s reaches it either, and no core-Lean statement without reals ever will; drawing the line at integer exponents leaves the same algebraic content of Art. 205 (a^x / a^y = a^(x−y)), now including negative logarithms and non-integral quotients.

2. **Relation, not function; a = 1.** Art. 205's argument is exactly what is formalised: suppose a^x = M and a^y = N, then a^(x−y) = M/N. Uniqueness of the logarithm, and so excluding a = 1, belongs to the definition in Art. 199, not to Art. 205, and the theorem remains true, not vacuous or false, for a = 1.

3. **Documentation.** The comments state plainly that "Exponents are now integers" and declare `z : Int` in the signature, so no reader is misled into thinking rational exponents are covered. A natural-number base is a positive rational, so "positive rational, not real" is accurate as a contrast with the reals, and Lean plus the challenger's NO OBJECTION confirm the code proves what it states.

## supervisor
REVISE. The critic's first and third points stand: limiting exponents to integers (and the base to a natural number) is a special case that the core library does not force. The defender's log₁₀ 2 example does not change this, because rational exponents still cover cases such as log₄ 2 = 1/2 and log₈ 4 = 2/3, which the current statement excludes. Generalise `IsLog` to a positive rational base and rational exponents encoded by cross-multiplication, add the hypothesis that the base is not 1, and correct the header comments so they state exactly what the base and exponents range over.

## prover
-- The supervisor's direction is followed and the code is repaired.
-- Scope of this version:
-- * The base is a positive rational a = a₁/a₂, with a₁ ≥ 1 and a₂ ≥ 1. It must not be 1,
--   so the hypothesis a₁ ≠ a₂ is included. This covers bases such as 1/2.
-- * The fractions M = m₁/m₂ and N = n₁/n₂ are positive rationals, compared by
--   cross-multiplication.
-- * Exponents are arbitrary rationals. An exponent is a triple (p, n, d) with d > 0 that
--   stands for (p - n)/d. Every rational number has this form, and negative values come
--   from n > p. So log₄ 2 = 1/2, log₈ 4 = 2/3 and negative or fractional logarithms are
--   all covered.
-- * `IsLog a F (p, n, d)` says that a ^ ((p - n)/d) = F. It is written without division as
--   (a₁/a₂)^(p - n) = (F.1/F.2)^d and then cross-multiplied:
--   a₁^p · a₂^n · F.2^d = a₂^p · a₁^n · F.1^d.
--   For positive F and d > 0 this matches the real statement, because positive d-th
--   roots are unique.
-- * The difference x - y of the exponents x = (r₁ - r₂)/s and y = (t₁ - t₂)/u is
--   ((r₁u + t₂s) - (r₂u + t₁s))/(su).
-- What is still out of scope:
-- * Irrational exponents and real bases, such as log₁₀ 2. The Lean core library has
--   no real numbers.
-- * Uniqueness of the logarithm. The theorem shows that x - y is a logarithm of M/N.
--   Uniqueness for a ≠ 1 belongs to Art. 199 and is not proved here.

/-- Art. 199: the rational exponent `e = (e.1 - e.2.1) / e.2.2` is a logarithm of the
fraction `F = F.1 / F.2` to the base `a = a.1 / a.2` when `a ^ e = F`, that is
`(a.1/a.2)^(e.1 - e.2.1) = (F.1/F.2)^(e.2.2)`, stated by cross-multiplication. -/
def IsLog (a F : Nat × Nat) (e : Nat × Nat × Nat) : Prop :=
  a.1 ^ e.1 * a.2 ^ e.2.1 * F.2 ^ e.2.2 = a.2 ^ e.1 * a.1 ^ e.2.1 * F.1 ^ e.2.2

/-- Quotient of the fractions `M = M.1 / M.2` and `N = N.1 / N.2`. -/
def fdiv (M N : Nat × Nat) : Nat × Nat := (M.1 * N.2, M.2 * N.1)

/-- Difference of the rational exponents `x = (r₁ - r₂)/s` and `y = (t₁ - t₂)/u`,
namely `((r₁u + t₂s) - (r₂u + t₁s)) / (su)`. -/
def esub (x y : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (x.1 * y.2.2 + y.2.1 * x.2.2, x.2.1 * y.2.2 + y.1 * x.2.2, x.2.2 * y.2.2)

/-- Art. 205. Let `a = a₁/a₂ ≠ 1` be a positive rational base. Let `M = m₁/m₂` and
`N = n₁/n₂` be positive fractions. If `x = log_a M` and `y = log_a N` are rational
exponents, that is `a ^ x = M` and `a ^ y = N`, then
`log_a (M / N) = x - y = log_a M - log_a N`. -/
theorem hk_art_205 (a₁ a₂ m₁ m₂ n₁ n₂ r₁ r₂ s t₁ t₂ u : Nat)
    (_ha₁ : 0 < a₁) (_ha₂ : 0 < a₂) (_ha : a₁ ≠ a₂)
    (_hm₁ : 0 < m₁) (_hm₂ : 0 < m₂) (_hn₁ : 0 < n₁) (_hn₂ : 0 < n₂)
    (_hs : 0 < s) (_hu : 0 < u)
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

## lean
Lean accepts the code.

## challenger
OBJECTION: Art. 205 asserts an equality of values, log_a(M/N) = log_a M − log_a N, where Art. 199 defines *the* logarithm. The final theorem only shows that `esub x y` is *a* logarithm of M/N, and the prover explicitly leaves uniqueness out of scope. As a result the newly added hypothesis `_ha : a₁ ≠ a₂` is unused and does no work. A uniqueness lemma is needed for the theorem to state the book's equation rather than a weaker existence claim: if `IsLog a F e` and `IsLog a F e'` with a ≠ 1, then e and e' are the same rational, (e.1 − e.2.1)·e'.2.2 = (e'.1 − e'.2.1)·e.2.2. That lemma can be stated and proved in core Lean by cross-multiplication.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The final code answers every point raised, and I can defend no further objection.

- **Definition of the logarithm.** `IsLog` faithfully encodes a^((p−n)/d) = F for a positive rational base and a positive rational F. Cross-multiplying gives a₁^p·a₂^n·F₂^d = a₂^p·a₁^n·F₁^d, which is equivalent to the real statement because positive d-th roots are unique.
- **Quotient and difference.** `fdiv` computes M/N correctly. `esub` computes x − y correctly as ((r₁u + t₂s) − (r₂u + t₁s))/(su).
- **The book's equation of values.** The theorem now states log_a(M/N) = log_a M − log_a N as an equality of values. It shows that x − y is a logarithm of M/N, and `isLog_unique` shows that every logarithm of M/N equals x − y as a rational.
- **The hypothesis a₁ ≠ a₂.** It is now used in the uniqueness proof. It excludes the base 1, for which the logarithm has no single value.
- **Zero-denominator triples.** A triple z with z.2.2 = 0 satisfies `IsLog` only when p = n, and then `ERel` holds trivially. So such triples cannot falsify the uniqueness clause or make it vacuous.
- **Scope and header.** The header states the scope accurately: a positive rational base other than 1, positive rational M and N, and arbitrary rational exponents. Irrational exponents are excluded only because the core library has no real numbers, and the supervisor accepted that limit.
- **Lean check.** Lean accepts the code.

## critic
# Critic: hk_art_205 should not merge

1. **`IsLog`, the formalisation of Art. 199, is wrong for zero-denominator triples, and the uniqueness clause depends on that defect.**
   - Neither `IsLog` nor `ERel` requires `e.2.2 > 0`. For the triple `(p, p, 0)`, which stands for 0/0, `IsLog a F (p, p, 0)` reduces to `a₁^p·a₂^p·1 = a₂^p·a₁^p·1`. That is true for **every** F. So the definition declares the non-number 0/0 to be a logarithm of every fraction to every base.
   - `ERel (p, p, 0) e` reduces to `p·e.2.2 = p·e.2.2`. That is true for every e. So `ERel` is not transitive, and it does not express "the same rational", although the docstring says it does.
   - The second conjunct of `hk_art_205` quantifies over all triples `z` with no `0 < z.2.2`. Its claim that "every logarithm of M/N equals x − y as a rational" is therefore partly satisfied by junk triples that are not exponents at all.
   - The challenger's final sign-off says zero-denominator triples "cannot falsify the uniqueness clause or make it vacuous." That is true only because the defective `ERel` absorbs the defective `IsLog`. The challenger accepted the defect as if it were a fix.
   - `_hs` and `_hu` are still unused, underscored hypotheses. The existence part never needs `s, u > 0`. So the theorem never ties its "rational exponent" reading to actual rationals.

2. **The stated equation of values is still a conditional claim about a narrow special case, and core Lean does not force that.**
   - Art. 205 holds for any positive M and N, with x and y their real logarithms. The proof the book gives uses only the index law a^x / a^y = a^(x−y).
   - That article can be stated faithfully in core Lean without ℝ. One way is to parametrise over an exponent type with a power operation satisfying the earlier index laws, for example a structure or typeclass hypothesis. That form includes the real case the book means.
   - The final code instead fixes the exponents to rationals. Its hypotheses `hx` and `hy` are therefore unsatisfiable for log₁₀ 2, log₂ 3, and almost every value the logarithm chapter is about.
   - The supervisor's direction was to widen the scope as far as core Lean allows. It asked for rational exponents because the defender claimed nothing wider was possible. That claim was never tested against an abstract statement.

3. **The prover's answer to the last objection was checked only against the challenger's wording, not against the issue's prose.**
   - The challenger asked for uniqueness so that the theorem would state the book's "log_a(M/N) = log_a M − log_a N" as an equality of values. The prover supplied uniqueness with respect to a relation that is not an equality (point 1). The prover proved no lemma that `ERel` is an equivalence on triples with positive denominators.
   - The prover also proved no lemma that `IsLog` respects equality of fractions. That is the cross-multiplication equivalence of `(m₁, m₂)` and of `fdiv`. Without it, "log_a(M/N)" is not shown to depend on the fraction M/N rather than on the chosen numerator–denominator pair.
   - The header and docstrings ("the same rational", "every logarithm of M/N equals x − y as a rational") therefore claim more than the code proves. The final "NO OBJECTION" confirms only that the challenger's literal request was met. It does not confirm that Art. 205 is faithfully stated.
   - At minimum, before merging:
     - add `0 < e.2.2` to `IsLog`, or as a hypothesis on `z`;
     - prove that `ERel` is an equivalence on well-formed triples;
     - prove that `IsLog` is invariant under equivalent fraction representations.

## defender
**Defender: hk_art_205 should merge**

1. **Zero-denominator triples.** The uniqueness conjunct quantifies over every triple `z`, so it contains the version with `0 < z.2.2` as a special case; adding that hypothesis would only weaken the theorem, and the junk triples cannot make any conclusion false. For every `z` with a positive denominator, `ERel` is the standard cross-multiplication definition of equality of rationals, and `x`, `y` and `esub x y` all have positive denominators by `_hs` and `_hu`. So the claim "every logarithm of M/N equals x − y as a rational" is exactly what is proved for every exponent that is actually a rational.

2. **An abstract exponent type.** A typeclass that assumes the index laws would assume the book's step a^x / a^y = a^(x−y) as a field, which turns Art. 205 into a restatement of its own hypothesis. Core Lean also has no real model to instantiate it, so it would cover log₁₀ 2 in name only. The current code instead proves that law for every rational exponent, positive rational base and positive rational M and N, which is the scope the supervisor directed.

3. **Missing equivalence and invariance lemmas.** `IsLog` is homogeneous in `F.1` and `F.2`, and `ERel` on triples with positive denominators is literally the defining equation of rational equality. So invariance under equivalent representations and the equivalence-relation properties are standard facts about these encodings, not gaps in the statement of Art. 205. No docstring claims either lemma, and the merged theorem proves both halves of the book's equation of values for the quotient it names: existence, and uniqueness as a rational.

## supervisor
**MERGE.** Lean accepts the last code, and its encoding (a positive rational base other than 1, positive rational M and N, rational exponents with positive denominators by `_hs` and `_hu`) states both halves of Art. 205's equation of values: `esub x y` is a logarithm of M/N, and every logarithm of M/N equals it. The critic's zero-denominator triples cannot falsify that claim. For every z with a positive denominator, `ERel` is exact rational equality, so the universal clause contains the well-formed case; the abstract exponent typeclass would merely assume the index law the article proves. The equivalence and representation-invariance lemmas are standard facts about the cross-multiplication encoding, not part of what Art. 205 asserts, so no point of the critic stands.
