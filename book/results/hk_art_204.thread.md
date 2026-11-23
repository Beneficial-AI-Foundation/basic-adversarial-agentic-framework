## issue
Issue #204. To find the logarithm of a product (Art. 204)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XVI (Logarithms), Art. 204.
The book prints the following text.
199. DEFINITION. The logarithm of any number to a given base is the index of the power to which the base must be raised in order to equal the given number. Thus if a^x = N, x is called the logarithm of N to the base a.
200. The logarithm of N to base a is usually written log_a N, so that the same meaning is expressed by the two equations a^x = N; x = log_a N.
Let MN be the product; let a be the base of the system, and suppose x = log_a M, y = log_a N; so that a^x = M, a^y = N.
log_a MN = x + y = log_a M + log_a N. Similarly, log_a MNP = log_a M + log_a N + log_a P; and so on for any number of factors.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_204.

## prover
/-- `IsLog a N x` encodes Art. 199: `x` is a logarithm of `N` to the base `a`
when `a ^ x = N`. Core Lean has no real numbers, so the bases, numbers and
exponents here are natural numbers. -/
def IsLog (a N x : Nat) : Prop := a ^ x = N

/-- Hall and Knight, Higher Algebra, Art. 204 (logarithm of a product).

The first part says that if `x = log_a M` and `y = log_a N`, then
`log_a (M * N) = x + y`, the sum `log_a M + log_a N`.

The second part says the same for any number of factors. Suppose each
pair `(M, x)` in a list satisfies `x = log_a M`. Then the sum of the
logarithms is a logarithm of the product of the numbers.

This is stated for natural numbers only, since core Lean has no real
exponentiation. -/
theorem hk_art_204 :
    (∀ a M N x y : Nat, IsLog a M x → IsLog a N y → IsLog a (M * N) (x + y)) ∧
    (∀ (a : Nat) (l : List (Nat × Nat)), (∀ p ∈ l, IsLog a p.1 p.2) →
      IsLog a (l.foldr (fun p acc => p.1 * acc) 1)
              (l.foldr (fun p acc => p.2 + acc) 0)) := by
  constructor
  · intro a M N x y hx hy
    unfold IsLog at *
    rw [Nat.pow_add, hx, hy]
  · intro a l
    induction l with
    | nil =>
      intro _
      show a ^ 0 = 1
      exact Nat.pow_zero a
    | cons p t ih =>
      intro h
      have hp : IsLog a p.1 p.2 := h p (by simp)
      have ht : IsLog a (t.foldr (fun p acc => p.1 * acc) 1)
          (t.foldr (fun p acc => p.2 + acc) 0) :=
        ih (fun q hq => h q (by simp [hq]))
      unfold IsLog at hp ht
      show a ^ (p.2 + t.foldr (fun p acc => p.2 + acc) 0)
          = p.1 * t.foldr (fun p acc => p.1 * acc) 1
      rw [Nat.pow_add, hp, ht]

## lean
Lean accepts the code.

## challenger
OBJECTION: The encoding restricts bases, numbers and exponents to natural numbers. That makes the theorem cover only the case where M and N are exact non-negative integer powers of a, so it reduces to the identity a^(x+y) = a^x · a^y. Art. 204 concerns logarithms of arbitrary positive numbers, with fractional and negative logarithms such as log_10 2 or log_10 (1/10), and none of these is expressible here. Also, `IsLog` is a relation with no hypothesis a > 0, a ≠ 1, so the theorem only says x + y is *a* logarithm of MN (for a = 1 every z qualifies), not that log_a MN *equals* log_a M + log_a N as the book states.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The repaired theorem answers both of my earlier objections. Real powers fall under the abstract `pow` with the index laws, so fractional and negative logarithms are covered. The injectivity hypothesis gives uniqueness, so the conclusion is an equality, matching the book's claim that log_a MN equals log_a M + log_a N. I also checked that the hypotheses are not vacuous: `Nat.pow` with base 2 satisfies all three. The list form matches "and so on for any number of factors".

## critic
The pull request should not merge. Lean accepts the code, but it states the article in a form whose substance is assumed rather than proved, and nothing in the thread checks that the generalisation does what the prover says it does.

1. **The theorem assumes the result it is meant to state.** The repair turns Art. 204 into a statement about an arbitrary `pow : R → E → R`. Its hypotheses are `h_add : pow a (x + y) = pow a x * pow a y`, `h_zero` and `h_inj`. The first conclusion follows from `h_add` by one `rw`, and the uniqueness clause follows from `h_inj` by one `trans`. For the case the challenger raised (real bases, fractional and negative indices), the index law *is* the mathematical content. Hall and Knight's step "log_a MN = x + y" relies on the index law already being established for those exponents. The code assumes that law instead of establishing or importing it, so the theorem only restates its own hypotheses.

2. **The claim that real powers are covered is never verified.** The new docstring says that real powers, "including fractional and negative logarithms", are a special case. Core Lean has no reals, and no instance in the code shows this. The challenger's only non-vacuity check was `Nat.pow` with base 2. That is exactly the case the first objection complained about: natural-number exponents, where `log_10 (1/10)` and `log_10 2` cannot be expressed. No instance anywhere has a negative or fractional exponent; for example, `Int` exponents acting on some core type with inverses would have shown one. So the challenger's first objection was answered only by a comment. The withdrawal ("real powers fall under the abstract `pow`") accepts the prover's prose rather than anything Lean checked.

3. **The encoding no longer matches the book's setting, and the hypotheses are packaged opaquely.** In the book, the logarithm of a number N is defined only for a base a > 0 with a ≠ 1. This theorem replaces those conditions with an abstract injectivity axiom on an unspecified `pow` over arbitrary `Mul`/`Add` types. That axiom need not correspond to any base condition. The theorem also never requires M or N to be positive, and never relates `pow` to exponentiation at all: any injective additive-to-multiplicative map satisfies it.
   - The book's explicit three-factor form, `log_a MNP = log_a M + log_a N + log_a P`, is not stated. It appears only through a `foldr` encoding. Because `Mul R` and `Add E` are not assumed associative, the `foldr` encoding is not obviously the book's `M·N·P` or `x + y + z`. It fixes one particular bracketing.
   - The earlier `IsLog` definition, which encoded the issue's own Art. 199 definition, was removed. The final code therefore no longer states the definition the issue quotes.

   Together these problems leave the issue's request ("state the result of this article") unmet: what is certified is a lemma about abstract homomorphisms, not Hall and Knight's statement about logarithms.

## defender
**Defender's rebuttal: the pull request should merge.**

1. **"Assumes the result."** Art. 204's own proof is a single application of the index law a^x · a^y = a^(x+y), which Hall and Knight proved earlier in the chapter on indices and only cite here. Taking that law as a hypothesis reproduces the article's actual dependency, and a one-line proof of a one-line argument is faithful, not circular.

2. **"Real powers never verified."** The theorem is universally quantified over any `R`, `E` and `pow`, so Lean has checked that it holds for every structure satisfying the hypotheses. The only claim left unchecked is that real `a^x` with a > 0, a ≠ 1 satisfies the index laws and injectivity, which is exactly the background the book itself presupposes. Core Lean cannot formalise that fact, so a missing reals instance reflects the library's limits, not a gap in the statement.

3. **Setting mismatch.**
   - **Injectivity.** For a > 0, injectivity of x ↦ a^x is equivalent to a ≠ 1, and it is precisely what makes "log_a N" a well-defined value, so it encodes the book's base condition. Positivity of M and N is redundant because both are given as a^x and a^y.
   - **Three-factor form.** Instantiating the list as `[(M,x),(N,y),(P,z)]` gives `pow a (x+(y+(z+0))) = M*(N*(P*1))`, which is the book's MNP identity in the real setting, where + and · are associative and 0 and 1 are units. The book's unbracketed "MNP" presupposes associativity, so fixing one bracketing loses nothing it states.
   - **Removal of `IsLog`.** The hypotheses `pow a x = M` are Art. 199's "a^x = N" written out in full, so the definition is still stated, just not given a name. Naming it would not change the content.

## supervisor
**MERGE.** Lean accepts the final code, and the statement captures Art. 204: given a^x = M and a^y = N, it proves log_a MN = log_a M + log_a N as a uniquely determined value, and the list form covers any number of factors. The challenger's Nat base-2 instance shows the hypotheses are not vacuous. None of the critic's points stands: the book's proof itself just applies the previously established index law, taking that law as a hypothesis is faithful rather than circular, and the universal statement covers real powers even though core Lean cannot build that instance.
