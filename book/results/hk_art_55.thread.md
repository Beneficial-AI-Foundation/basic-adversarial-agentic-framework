## issue
Issue #55. To find the sum of a number of terms in Geometrical Progression (Art. 55)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter V (Geometrical Progression), Art. 55.
The book prints the following text.
51. DEFINITION. Quantities are said to be in Geometrical Progression when they increase or decrease by a constant factor.
The constant factor is also called the common ratio, and it is found by dividing any term by that which immediately precedes it.
Let a be the first term, r the common ratio, n the number of terms, and s the sum required. Then s = a + ar + ar^2 + ...... + ar^(n−2) + ar^(n−1);
s = a(r^n − 1)/(r − 1) ......(1). Changing the signs in numerator and denominator, s = a(1 − r^n)/(1 − r) ......(2).
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_55.

## prover
/-- Hall & Knight, *Higher Algebra*, Art. 55: the sum of `n` terms of a geometrical
progression with first term `a` and common ratio `r ≠ 1`, namely
`s = a + a r + a r^2 + ... + a r^(n-1)`, is `s = a (r^n - 1) / (r - 1)` (formula (1)).
Equivalently, `s = a (1 - r^n) / (1 - r)` (formula (2)).

This is stated over the integers `Int`, because the core library has no field of
rationals or reals. Here `/` is integer division. In both formulas the division is
exact, since `r - 1` (and `1 - r`) divides `a (r^n - 1)`. -/
def gpSum (a r : Int) : Nat → Int
  | 0 => 0
  | n + 1 => gpSum a r n + a * r ^ n

theorem gpSum_mul (a r : Int) (n : Nat) :
    gpSum a r n * (r - 1) = a * (r ^ n - 1) := by
  induction n with
  | zero => simp [gpSum]
  | succ n ih =>
    simp only [gpSum]
    rw [Int.add_mul, ih, Int.pow_succ]
    simp only [Int.mul_sub, Int.mul_one, ← Int.mul_assoc]
    generalize a * r ^ n = x
    generalize x * r = y
    omega

theorem gpSum_mul' (a r : Int) (n : Nat) :
    gpSum a r n * (1 - r) = a * (1 - r ^ n) := by
  have h := gpSum_mul a r n
  rw [Int.mul_sub, Int.mul_one, Int.mul_sub, Int.mul_one] at h
  rw [Int.mul_sub, Int.mul_one, Int.mul_sub, Int.mul_one]
  generalize gpSum a r n * r = u at *
  generalize a * r ^ n = v at *
  omega

/-- Hall & Knight, Art. 55: for `r ≠ 1`, the sum `s = a + a r + ... + a r^(n-1)` of `n`
terms of a geometrical progression satisfies `s = a (r^n - 1)/(r - 1)` and
`s = a (1 - r^n)/(1 - r)`. These are stated over `Int`, where both divisions are exact. -/
theorem hk_art_55 (a r : Int) (n : Nat) (hr : r ≠ 1) :
    gpSum a r n = a * (r ^ n - 1) / (r - 1) ∧
    gpSum a r n = a * (1 - r ^ n) / (1 - r) := by
  have h1 : r - 1 ≠ 0 := by omega
  have h2 : 1 - r ≠ 0 := by omega
  constructor
  · rw [← gpSum_mul, Int.mul_ediv_cancel _ h1]
  · rw [← gpSum_mul', Int.mul_ediv_cancel _ h2]

## lean
Lean accepts the code.

## challenger
OBJECTION The theorem is stated only for integer `a` and `r`, so it is strictly weaker than the book's claim about arbitrary quantities. Art. 51 explicitly covers progressions that "decrease by a constant factor", such as 1, 1/2, 1/4, …. Over `Int` the only ratio with |r| < 1 is r = 0, so such progressions cannot be stated at all, and formula (2), which the book writes for that case, is reduced to a statement about exact integer division. The theorem should be stated over a field such as `Rat`, or over an arbitrary commutative ring or field (for example via core's `Lean.Grind` field classes), using real division.

## prover
/-- Hall & Knight, *Higher Algebra*, Art. 55: let `a` be the first term, `r ≠ 1` the
common ratio and `n` the number of terms of a geometrical progression. Then the sum
`s = a + a r + a r^2 + ... + a r^(n-1)` satisfies
`s = a (r^n - 1) / (r - 1)` (formula (1)) and `s = a (1 - r^n) / (1 - r)` (formula (2)).

The statement holds over an arbitrary field `α`, given by core's `Lean.Grind.Field`, so
`/` is true field division. This covers rational and real quantities, and also
decreasing progressions such as `1, 1/2, 1/4, ...`. -/
def gpSum {α : Type u} [Lean.Grind.Field α] (a r : α) : Nat → α
  | 0 => 0
  | n + 1 => gpSum a r n + a * r ^ n

theorem gpSum_mul {α : Type u} [Lean.Grind.Field α] (a r : α) (n : Nat) :
    gpSum a r n * (r - 1) = a * (r ^ n - 1) := by
  induction n with
  | zero =>
    simp only [gpSum]
    rw [Lean.Grind.Semiring.pow_zero]
    grind
  | succ n ih =>
    simp only [gpSum]
    rw [Lean.Grind.Semiring.pow_succ]
    grind

/-- Hall & Knight, Art. 55: over any field, for `r ≠ 1`, the sum
`s = a + a r + ... + a r^(n-1)` of `n` terms of a geometrical progression satisfies
`s = a (r^n - 1)/(r - 1)` and `s = a (1 - r^n)/(1 - r)`. -/
theorem hk_art_55 {α : Type u} [Lean.Grind.Field α] (a r : α) (n : Nat) (hr : r ≠ 1) :
    gpSum a r n = a * (r ^ n - 1) / (r - 1) ∧
    gpSum a r n = a * (1 - r ^ n) / (1 - r) := by
  have h := gpSum_mul a r n
  have h1 : r - 1 ≠ 0 := by
    intro h0
    apply hr
    grind
  have h2 : 1 - r ≠ 0 := by
    intro h0
    apply hr
    grind
  constructor
  · grind
  · grind

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The prover's revision answers my earlier objection: the theorem now holds over any `Lean.Grind.Field`, so `/` is true field division and decreasing progressions such as 1, 1/2, 1/4, … are covered. `gpSum a r n` is by its recursive definition exactly a + ar + … + ar^(n−1), and the hypothesis `r ≠ 1` is exactly the condition the book needs to divide by r − 1 or 1 − r. Both formulas (1) and (2) appear in the conclusion. The extra case n = 0 is true (both sides are 0) and only strengthens the statement, and Lean accepts the code.

## critic
I argue against merging. I accept that Lean checks the code and that the formulas are true. My case is that the final code does not faithfully state Art. 55, and that the challenger accepted the revision too quickly.

1. **The theorem assumes the progression and the identity it should establish.** Art. 51 defines a geometrical progression by a constant ratio: each term divided by the one before gives the same factor. `hk_art_55` never refers to such a sequence. It quantifies over `a`, `r` and a function `gpSum` that is defined from the start as `Σ a * r ^ k`. The reader must check by eye that this is "the sum of n terms of a G.P.". Nothing in Lean links an arbitrary sequence with constant ratio `r` and first term `a` to `gpSum a r n`. The book's left-hand side is "s, the sum required" of a progression. In the code, the left-hand side is already a closed geometric expression. A faithful statement would take a sequence `t : Nat → α` with `t 0 = a` and `t (k+1) = t k * r`, sum `n` of its terms, and conclude both formulas.

2. **The prover never showed that the generalization covers the case the challenger raised.** The objection was that decreasing progressions with rational or real terms, such as 1, 1/2, 1/4, …, could not be stated over `Int`. The prover answered by abstracting to `[Lean.Grind.Field α]`. The docstring then claims that this "covers rational and real quantities". However:
   - Core has no reals at all.
   - The code never instantiates the theorem at any concrete field.
   - No example such as `hk_art_55 (1 : Rat) (1/2) 3 (by decide)` is checked.
   
   An abstract theorem over a typeclass with no exhibited instance in the build is only a promise of generality, not a demonstration of it. The challenger's withdrawal rests on a docstring claim that Lean never checked. The objection was concrete, so the answer should have been too.

3. **The statement does not capture the book's limited role for division and its two formulas.** Lean's field division sets `x / 0 = 0`. The hypothesis `r ≠ 1` is therefore what keeps the conjunction from being trivially odd, but it does not express the book's distinction:
   - formula (1) is for r > 1;
   - formula (2) is "changing the signs" for r < 1, the convergent case used later in Art. 56–57.
   
   The real mathematical content is `gpSum_mul`, the subtract-after-multiplying-by-r identity s(r−1) = a(rⁿ−1). This identity holds in any commutative ring, as the challenger's own suggestion noted. The prover demoted it to a helper lemma and did not state its formula (2) analogue as a lemma. Both division forms in the main theorem are then closed by `grind`, so a reviewer cannot see the derivation in the article, multiplying by r and subtracting, reflected in the proof. The challenger's "NO OBJECTION" checked only that both formulas appear. It did not check that the article's stated result (s(r−1) = a(rⁿ−1), valid without division) is what the theorem records.

For these reasons, the pull request should not merge as it stands.

## defender
The pull request should merge. Each point is rebutted below in at most two sentences, and none needs to be conceded.

**1. The progression and the sum.** The book itself states the sum required as `s = a + ar + ar^2 + ... + ar^(n−1)` before deriving (1) and (2), and `gpSum` encodes exactly that expression by recursion, so the left-hand side is the book's own. The fact that a sequence with `t 0 = a` and `t (k+1) = t k * r` has `k`-th term `a r^k` comes from the earlier article on the nth term, not Art. 55, so requiring it here would formalize more than the article states.

**2. No concrete instance is exhibited.** A theorem over every `Lean.Grind.Field` is a checked statement about every field, including any rational or real field, so generality needs no example to hold. An instantiation such as `Rat` with `r = 1/2` would be a test, not a correction, and the docstring's mention of reals refers to any real field one supplies, not a claim that core contains one.

**3. Division and the two formulas.**
- The book's remark that (1) suits r > 1 and (2) suits r < 1 is advice on which form to use, not a hypothesis, since both formulas hold for every r ≠ 1, exactly as stated. Because `r ≠ 1` makes both denominators nonzero, the `x / 0 = 0` convention never matters.
- The article's stated result is the pair of closed forms, which the main theorem records. The multiply-by-r-and-subtract identity s(r−1) = a(rⁿ−1) is present and proved as `gpSum_mul`, and closing steps with `grind` affects readability, not faithfulness.

## supervisor
MERGE. Lean accepts the final code, and `hk_art_55` states both formulas (1) and (2) for `r ≠ 1` over an arbitrary `Lean.Grind.Field`, with `gpSum a r n` being exactly the book's sum `a + ar + … + ar^(n−1)`. None of the critic's points stands: the article itself defines s as that explicit sum, a theorem proved for every field needs no concrete instance, and the r > 1 versus r < 1 remark is only advice on which form to use, while the multiply-and-subtract identity is proved as `gpSum_mul`.
