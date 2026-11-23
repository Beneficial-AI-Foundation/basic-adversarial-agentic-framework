-- Reply to the supervisor's REVISE.
-- (1) The comments overstated the result. Core Lean has neither real numbers nor a
--     field class, so this file proves only a special case of Art. 57.
--     * The ratio is a rational proper fraction r = p/q, with p an integer, q natural
--       and |p| < q. Negative ratios are included. Irrational ratios are not covered.
--     * The first term is a rational number a = a₁/b, with a₁ an integer and b > 0.
--       This is `hk_art_57`. The integer case b = 1 is `hk_art_57_int`.
--     * The tolerance is a fraction e/d. This loses nothing, because every positive
--       real ε contains such a fraction.
-- (2) The book's identity s = a/(1-r) - a r^n/(1-r) is now the named lemma
--     `gp_remainder`. It states it in cross-multiplied form: the n-term sum minus
--     a/(1-r), times q^n (q-p), equals -(a p^n q). Dividing by q^n (q-p) gives
--     -a r^n/(1-r) exactly.
-- (3) The unused hypothesis `0 < d` is dropped, which makes the statement stronger.
--     For d = 0 the claim is trivially true, since the right side is positive.

/-- `sumTo f n = f 0 + f 1 + … + f (n-1)`. -/
def sumTo (f : Nat → Int) : Nat → Int
  | 0 => 0
  | m + 1 => sumTo f m + f m

/-- An auxiliary recursion for `Σ_{k<n} p^k * q^(n-k)`. -/
def gpT (p : Int) (q : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => (q : Int) * gpT p q n + p ^ n * (q : Int)

theorem int_pow_one (x : Int) : x ^ 1 = x := by
  first
    | exact Int.pow_one _
    | (show (1 : Int) * x = x; exact Int.one_mul _)
    | (rw [Int.pow_succ, Int.pow_zero, Int.one_mul])

theorem sumTo_shift (p : Int) (q : Nat) (n : Nat) :
    ∀ m : Nat, m ≤ n → sumTo (fun k => p ^ k * (q : Int) ^ (n + 1 - k)) m
      = (q : Int) * sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) m
  | 0, _ => by simp [sumTo]
  | m + 1, h => by
    have ih := sumTo_shift p q n m (by omega)
    have e : n + 1 - m = (n - m) + 1 := by omega
    show sumTo (fun k => p ^ k * (q : Int) ^ (n + 1 - k)) m + p ^ m * (q : Int) ^ (n + 1 - m)
      = (q : Int) * (sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) m + p ^ m * (q : Int) ^ (n - m))
    rw [ih, e, Int.pow_succ (q : Int) (n - m), Int.mul_add]
    congr 1
    rw [Int.mul_comm (q : Int) (p ^ m * (q : Int) ^ (n - m)), Int.mul_assoc]

/-- The recursion `gpT` equals the explicit sum `Σ_{k<n} p^k * q^(n-k)`. -/
theorem gpT_eq_sum (p : Int) (q : Nat) :
    ∀ n : Nat, gpT p q n = sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) n
  | 0 => rfl
  | n + 1 => by
    show (q : Int) * gpT p q n + p ^ n * (q : Int)
      = sumTo (fun k => p ^ k * (q : Int) ^ (n + 1 - k)) n + p ^ n * (q : Int) ^ (n + 1 - n)
    rw [gpT_eq_sum p q n, sumTo_shift p q n n (Nat.le_refl n)]
    have e : n + 1 - n = 1 := by omega
    rw [e, int_pow_one]

theorem gpT_id (p : Int) (q : Nat) :
    ∀ n : Nat, gpT p q n * ((q : Int) - p) + p ^ n * (q : Int) = (q : Int) ^ (n + 1)
  | 0 => by
    have h := int_pow_one (q : Int)
    simp [gpT, h]
  | n + 1 => by
    have ih := gpT_id p q n
    have hp : p ^ (n + 1) = p ^ n * p := by
      first
        | rfl
        | exact Int.pow_succ p n
        | simp [Int.pow_succ]
    have hq : (q : Int) ^ (n + 1 + 1) = (q : Int) ^ (n + 1) * (q : Int) := by
      first
        | rfl
        | exact Int.pow_succ _ _
        | simp [Int.pow_succ]
    show ((q : Int) * gpT p q n + p ^ n * (q : Int)) * ((q : Int) - p) + p ^ (n + 1) * (q : Int)
      = (q : Int) ^ (n + 1 + 1)
    rw [hp, hq, ← ih]
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc,
      Int.mul_comm, Int.mul_left_comm] <;> omega

/-- The book's identity `s = a/(1 - r) - a r^n/(1 - r)` for `r = p/q`, cross-multiplied.
Here `S_n = a * T / q^n`, with `T = Σ_{k<n} p^k q^(n-k)`.
The lemma states `(S_n - a/(1-r)) * q^n * (q - p) = -(a p^n q)`.
Dividing by `q^n (q - p)` gives exactly `S_n - a/(1-r) = -a r^n / (1 - r)`. -/
theorem gp_remainder (a p : Int) (q n : Nat) :
    a * sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) n * ((q : Int) - p)
      - a * (q : Int) ^ (n + 1) = -(a * (p ^ n * (q : Int))) := by
  rw [← gpT_eq_sum p q n]
  have E3 := gpT_id p q n
  rw [← E3]
  simp only [Int.mul_add, Int.mul_assoc] <;> omega

theorem bern (p q u : Nat) (h : q = p + u) :
    ∀ n : Nat, p ^ n * (q + n * u) ≤ q ^ (n + 1)
  | 0 => by simp
  | n + 1 => by
    have ih := bern p q u h n
    have h1 : p ^ n * (q + n * u) * p ≤ q ^ (n + 1) * p :=
      Nat.mul_le_mul ih (Nat.le_refl p)
    have h2 : p ^ (n + 1) ≤ q ^ (n + 1) := Nat.pow_le_pow_left (by omega) (n + 1)
    have h3 : p ^ (n + 1) * u ≤ q ^ (n + 1) * u := Nat.mul_le_mul h2 (Nat.le_refl u)
    have e1 : p ^ (n + 1) * (q + (n + 1) * u) = p ^ n * (q + n * u) * p + p ^ (n + 1) * u := by
      rw [Nat.pow_succ]
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm]
      all_goals omega
    have e0 : q ^ (n + 1 + 1) = q ^ (n + 1) * q := by
      first
        | rfl
        | rw [Nat.pow_succ]
    have e2 : q ^ (n + 1 + 1) = q ^ (n + 1) * p + q ^ (n + 1) * u := by
      rw [e0, ← Nat.mul_add, ← h]
    omega

theorem my_pow_pos (q : Nat) (h : 0 < q) : ∀ n : Nat, 0 < q ^ n
  | 0 => by simp
  | n + 1 => by rw [Nat.pow_succ]; exact Nat.mul_pos (my_pow_pos q h n) h

/-- Special case of Hall & Knight, Art. 57, with an integer first term `a`.
The ratio is the rational proper fraction `r = p/q`, with `|p| < q`.
`S_n = a * T / q^n`, where `T = Σ_{k<n} p^k q^(n-k)` is the n-term sum.
For every tolerance `e/d`, there is an `N` such that for all `n ≥ N`,
`|S_n - a/(1-r)| < e/d`, stated cross-multiplied.
The case `d = 0` is allowed and holds trivially. -/
theorem hk_art_57_int (a p : Int) (q : Nat) (hpq : p.natAbs < q) (e d : Nat) (he : 0 < e) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      d * Int.natAbs (a * sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) n * ((q : Int) - p)
          - a * (q : Int) ^ (n + 1))
        < e * Int.natAbs ((q : Int) ^ n * ((q : Int) - p)) := by
  refine ⟨d * a.natAbs * q * q + 1, ?_⟩
  intro n hn
  rw [gp_remainder a p q n]
  have hq : 0 < q := by omega
  have hA : Int.natAbs (-(a * (p ^ n * (q : Int)))) = a.natAbs * (p.natAbs ^ n * q) := by
    first
      | (rw [Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_pow]; rfl)
      | simp [Int.natAbs_mul, Int.natAbs_pow]
  have hB : Int.natAbs ((q : Int) ^ n * ((q : Int) - p))
      = q ^ n * ((q : Int) - p).natAbs := by
    first
      | (rw [Int.natAbs_mul, Int.natAbs_pow]; rfl)
      | simp [Int.natAbs_mul, Int.natAbs_pow]
  have hlt : p < (q : Int) := by
    first
      | omega
      | (have := Int.le_natAbs (a := p); omega)
  have hw : 0 < ((q : Int) - p).natAbs := by
    first
      | omega
      | exact Int.natAbs_pos.mpr (by omega)
  rw [hA, hB]
  generalize ((q : Int) - p).natAbs = w at hw ⊢
  generalize a.natAbs = A at hn ⊢
  generalize p.natAbs = P at hpq ⊢
  obtain ⟨u, hu⟩ : ∃ u, q = P + u := ⟨q - P, by omega⟩
  have hu1 : 1 ≤ u := by omega
  have B := bern P q u hu n
  have B' : P ^ n * (q + n * u) ≤ q ^ n * q := by rw [← Nat.pow_succ]; exact B
  have hQ := my_pow_pos q hq n
  have fA : q ^ n * q ≤ e * (q ^ n * w) * q := by
    have h0 : e * (q ^ n * w) * q = (e * w) * (q ^ n * q) := by
      first
        | ac_rfl
        | simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have h1 : 1 * (q ^ n * q) ≤ (e * w) * (q ^ n * q) :=
      Nat.mul_le_mul (Nat.mul_pos he hw) (Nat.le_refl _)
    omega
  have fC : P ^ n * n ≤ P ^ n * (q + n * u) := by
    have h1 : n * 1 ≤ n * u := Nat.mul_le_mul (Nat.le_refl n) hu1
    have h3 : n ≤ q + n * u := by omega
    exact Nat.mul_le_mul (Nat.le_refl _) h3
  have fD : P ^ n * (d * A * q * q + 1) ≤ P ^ n * n := Nat.mul_le_mul (Nat.le_refl _) hn
  have fE : P ^ n * (d * A * q * q + 1) = P ^ n * (d * A * q * q) + P ^ n := by
    rw [Nat.mul_add, Nat.mul_one]
  have fF : d * (A * (P ^ n * q)) * q = P ^ n * (d * A * q * q) := by
    first
      | ac_rfl
      | simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have fG : 0 < e * (q ^ n * w) * q :=
    Nat.mul_pos (Nat.mul_pos he (Nat.mul_pos hQ hw)) hq
  have fH : 0 < P ^ n ∨ P ^ n * (d * A * q * q) = 0 := by
    rcases Nat.eq_zero_or_pos (P ^ n) with h | h
    · right; rw [h, Nat.zero_mul]
    · left; exact h
  have key : d * (A * (P ^ n * q)) * q < e * (q ^ n * w) * q := by omega
  exact Nat.lt_of_mul_lt_mul_right key

/-- Hall & Knight, Art. 57 (sum to infinity of a decreasing G.P.).
This is the special case of a rational ratio and a rational first term.
Irrational values are not covered, because core Lean has no real numbers.
Let the first term be `a = a₁/b`, with `a₁` an integer and `b > 0`.
Let the ratio be the proper fraction `r = p/q`, with `p` an integer, `q` natural and `|p| < q`.
Negative ratios are allowed.
Term k is `a r^k = a₁ p^k q^(n-k) / (b q^n)`.
So `S_n = a₁ * T / (b q^n)`, where `T = Σ_{k<n} p^k q^(n-k)` is written with `sumTo`.
The sum to infinity is `a/(1-r) = a₁ q / (b (q - p))`.
Hence `S_n - a/(1-r) = (a₁ T (q-p) - a₁ q^(n+1)) / (b q^n (q-p))`.
For every positive tolerance `e/d`, and for all sufficiently large `n`,
the absolute value of this difference is less than `e/d`.
The inequality is stated cross-multiplied, with no division.
The case `d = 0` is allowed and holds trivially. -/
theorem hk_art_57 (a₁ p : Int) (b q : Nat) (hb : 0 < b) (hpq : p.natAbs < q)
    (e d : Nat) (he : 0 < e) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      d * Int.natAbs (a₁ * sumTo (fun k => p ^ k * (q : Int) ^ (n - k)) n * ((q : Int) - p)
          - a₁ * (q : Int) ^ (n + 1))
        < e * (b * Int.natAbs ((q : Int) ^ n * ((q : Int) - p))) := by
  obtain ⟨N, hN⟩ := hk_art_57_int a₁ p q hpq (e * b) d (Nat.mul_pos he hb)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Nat.mul_assoc] at h1
  exact h1
