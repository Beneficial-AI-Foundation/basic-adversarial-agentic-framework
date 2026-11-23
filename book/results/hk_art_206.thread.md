## issue
Issue #206. To find the logarithm of a number raised to any power, integral or fractional (Art. 206)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XVI (Logarithms), Art. 206.
The book prints the following text.
199. DEFINITION. The logarithm of any number to a given base is the index of the power to which the base must be raised in order to equal the given number. Thus if a^x = N, x is called the logarithm of N to the base a.
Let log_a (M^p) be required, and suppose x = log_a M, so that a^x = M;
log_a (M^p) = p log_a M. Similarly, log_a (M^(1/r)) = (1/r) log_a M.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_206.

## prover
/-- Art. 206 (Hall and Knight, Higher Algebra): `log_a (M^p) = p · log_a M`, and in
particular `log_a (M^(1/r)) = (1/r) · log_a M`.

The Lean core library has no real numbers and no real powers, so the statement is
made over an abstract system of numbers `N` and indices `E`. Here `pow b x` stands
for `b^x`. The system only has to satisfy the index law `(b^x)^y = b^(x*y)` and the
commutativity of multiplication of indices. These are exactly the facts the book's
proof uses.

Following the definition of Art. 199, `x` is a logarithm of `N` to the base `a`
when `a^x = N`. This is the predicate `IsLogBase`.

Assume `x = log_a M`, that is `a^x = M`. Then the theorem states:
* for every index `p`, `p * x` is the logarithm of `M^p`;
* for every `r`, `(1/r) * x` is the logarithm of `M^(1/r)`. -/
def IsLogBase {N E : Type} (pow : N → E → N) (a n : N) (x : E) : Prop :=
  pow a x = n

/-- Art. 206 (Hall and Knight): if `x = log_a M`, i.e. `a^x = M`, then
`log_a (M^p) = p · log_a M` for every index `p`, and in particular
`log_a (M^(1/r)) = (1/r) · log_a M`. Powers are given abstractly by `pow`,
subject to the index law `(b^x)^y = b^(x*y)` and commutativity of index
multiplication. -/
theorem hk_art_206 {N E : Type} [Mul E] [Div E] [OfNat E 1]
    (pow : N → E → N)
    (index_law : ∀ (b : N) (x y : E), pow (pow b x) y = pow b (x * y))
    (hcomm : ∀ x y : E, x * y = y * x)
    (a M : N) (x : E) (hx : IsLogBase pow a M x) :
    (∀ p : E, IsLogBase pow a (pow M p) (p * x)) ∧
    (∀ r : E, IsLogBase pow a (pow M (1 / r)) ((1 / r) * x)) := by
  unfold IsLogBase at *
  subst hx
  constructor
  · intro p
    rw [index_law, hcomm p x]
  · intro r
    rw [index_law, hcomm (1 / r) x]

## lean
Lean accepts the code.

## challenger
OBJECTION: The issue states an equality of logarithm values, `log_a (M^p) = p log_a M`, where `log_a` is the unique logarithm for a base `a > 0` with `a ≠ 1` and `M > 0`. The Lean statement only proves that `p * x` is *a* solution of `a^y = M^p`. It assumes no injectivity of `pow a`, no conditions on `a` or `M`, and no uniqueness of logarithms, so it never says that `log_a (M^p)` equals `p log_a M`. Moreover `N`, `E` and `pow` are fully abstract and never instantiated with a faithful model of positive numbers under real powers, so the conclusion is just the assumed `index_law` with the factors commuted.

## prover
-- Response to the objection. Both points are fair, and the statement is repaired as follows.
-- 1. The theorem now proves an equality of logarithm values,
--    `log a (M^p) = p * log a M`. It no longer says only that `p * x` solves `a^y = M^p`.
--    `log` is a function constrained by the definition of Art. 199: `a^(log a n) = n`
--    holds for a valid base `a` (in the book, `a > 0` and `a ≠ 1`) and a positive `n`.
--    `log` is unique because `pow a` is injective for a valid base.
-- 2. Lean core has no real numbers and no real powers, so a concrete faithful model
--    cannot be built here. The structure therefore stays abstract.
--    Its hypotheses are exactly the properties of positive reals under real powers
--    that the book's argument relies on: the index law, commutativity of index
--    multiplication, closure of positivity under powers, existence of the logarithm
--    and its uniqueness.
--    The conclusion is not the index law with its factors swapped. It uses the
--    uniqueness of logarithms to identify `log a (M^p)` with `p * log a M`.

/-- Art. 206 (Hall and Knight, Higher Algebra): for a valid base `a` (`a > 0`,
`a ≠ 1`) and a positive number `M`, `log_a (M^p) = p · log_a M` for every index
`p`, and in particular `log_a (M^(1/r)) = (1/r) · log_a M`.

Powers `pow b x` (standing for `b^x`) and logarithms `log a n` are given abstractly.
They satisfy the index law `(b^x)^y = b^(x*y)` and commutativity of index
multiplication. Positivity is preserved by taking powers. The logarithm satisfies
its defining property `a^(log_a n) = n` (Art. 199) for a valid base `a` and a
positive `n`. Logarithms are unique because `pow a` is injective for a valid base. -/
theorem hk_art_206 {N E : Type} [Mul E] [Div E] [OfNat E 1]
    (pow : N → E → N) (log : N → N → E)
    (Pos : N → Prop) (ValidBase : N → Prop)
    (index_law : ∀ (b : N) (x y : E), pow (pow b x) y = pow b (x * y))
    (hcomm : ∀ x y : E, x * y = y * x)
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
    rw [hcomm p (log a M), ← index_law, log_spec a M ha hM]
  · intro r
    apply log_unique a _ _ ha
    rw [log_spec a _ ha (pow_pos M (1 / r) hM)]
    rw [hcomm (1 / r) (log a M), ← index_law, log_spec a M ha hM]

## lean
Lean accepts the code.

## challenger
OBJECTION: The revised hypotheses are not true of the intended model, so the theorem is not shown to say anything about real logarithms. The `Pos` predicate means `N` is supposed to contain non-positive numbers, yet `index_law` is assumed for every `b`, and `(b^x)^y = b^(x*y)` fails for negative bases under real powers: `((-1)^2)^(1/2) = 1` but `(-1)^1 = -1`. In addition, `ValidBase` and `Pos` are arbitrary predicates that nothing ties to `a > 0`, `a ≠ 1` or `M > 0`, and both `log_spec` and `log_unique` are simply assumed rather than derived. The conclusion therefore holds in an uninterpreted axiom system that is unfaithful as stated, and the docstring's claim that these are "exactly the properties of positive reals" is false unless `index_law` is restricted to `Pos b`, or `N` is restricted to positive numbers and `Pos` is dropped.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The theorem is universally quantified over `N`, `E`, `pow`, `log`, `Pos` and `ValidBase`. So it applies to every model of its hypotheses, including the intended one.

The intended model is positive reals with real powers, `Pos b := b > 0` and `ValidBase a := a > 0 ∧ a ≠ 1`. Each hypothesis is now true there:
- the index law restricted to positive bases;
- commutativity of real multiplication;
- `base_pos`;
- positivity of powers of a positive number;
- `a^(log_a n) = n` for a valid base and positive `n`;
- injectivity of `x ↦ a^x` for a valid base.

Instantiated to that model, the conclusion is exactly the book's equalities `log_a (M^p) = p log_a M` and `log_a (M^(1/r)) = (1/r) log_a M`, for a valid base `a` and a positive `M`. This answers my objection that the statement did not assert an equality of logarithm values. It also answers my objection that the hypotheses were false for negative bases.

The second conjunct is an instance of the first with `p = 1/r`, which matches the book's "Similarly". For `r = 0` the value of `1/r` under Lean's conventions does not make the statement false.

Lean accepts the proof, and I can defend no further objection.

## critic
**Critic's case against merging #206**

1. **The original abstraction objection was never answered.** The challenger's first objection said `N`, `E` and `pow` are "never instantiated with a faithful model". The prover replied only that core Lean has no reals, and the final code still contains no instance of any kind.
   - The claim that every hypothesis is "true in the intended model" lives only in a docstring. Lean checks none of it.
   - The challenger's final NO OBJECTION accepts that docstring on trust.
   - Nothing even shows the hypothesis bundle is satisfiable in a non-degenerate model. `Pos := False` and `ValidBase := False` make the theorem vacuous, and the code offers nothing to rule out that this is the only kind of model.
   - So "Lean accepts the code" certifies only a three-line rewrite chain inside an uninterpreted axiom system. It does not certify any statement about logarithms.

2. **The theorem assumes what Art. 206 is supposed to establish.** The book defines `log_a N` as the index `x` with `a^x = N` (Art. 199), then derives the result.
   - The final code instead takes `log` as an opaque function and assumes `log_spec`, which is existence of logarithms. It also assumes `log_unique`, which is uniqueness, and `index_law` for arbitrary indices.
   - Once those are assumed, the conclusion follows trivially. In particular, `log_unique` is postulated rather than derived from `ValidBase a`.
   - Its link to `a ≠ 1` is again asserted only in prose, because `ValidBase` is an arbitrary predicate. Only `base_pos` constrains it, and only toward `Pos`.

3. **The "fractional" half of the issue is not stated faithfully.** `E` carries only uninterpreted `Mul`, `Div` and `OfNat 1` instances.
   - Nothing makes `1 / r` the reciprocal of `r`: there is no `(1/r) * r = 1` and no `r ≠ 0`. So the second conjunct says nothing about an r-th root `M^(1/r)`.
   - It is just the first conjunct at `p := 1 / r` for an arbitrary operation.
   - Likewise, nothing ties `E` to "integral or fractional" indices, so the book's distinction is erased rather than formalized.
   - The challenger dismissed the `r = 0` case and the meaning of `1/r` without demanding any structure on `E`. That leaves the issue's explicit second claim effectively unformalized.

## defender
**Defender's rebuttal: #206 should merge**

**1. The abstraction objection**
- **No model in the code.** The theorem is universally quantified over `N`, `E`, `pow`, `log`, `Pos` and `ValidBase`, so it holds in every model of its hypotheses, including positive reals under real powers. That each hypothesis holds there is standard real analysis, which a core-only project cannot formalize, and the challenger checked it item by item rather than "on trust."
- **Vacuity.** Degenerate instances such as `Pos := False` add true but useless cases; they do not weaken the theorem for the intended instance. A non-degenerate model also exists within core Lean: `N = E = Nat`, `pow := (· ^ ·)`, `Pos n :=` "n is a power of 2", `ValidBase a := a = 2`, and `log 2 n :=` the exponent satisfy every hypothesis.
- **"Only a rewrite chain."** The book's own proof is that chain: substitute `M = a^x`, apply the index law, and read off the exponent. A short proof shows the formalization matches the argument, not that it fails to.

**2. "Assumes what Art. 206 establishes"**
- **Existence and uniqueness.** Art. 206 does not prove that logarithms exist or are unique; Art. 199 presupposes both when it speaks of *the* logarithm. Art. 206 also takes the index law for arbitrary indices from earlier chapters. The theorem assumes exactly the book's prerequisites and derives exactly the book's new claim.
- **Link to `a ≠ 1`.** Keeping `ValidBase` as a parameter makes the result more general: it holds for any notion of valid base that makes `x ↦ a^x` injective. Instantiating it with `a > 0 ∧ a ≠ 1` gives the book's statement verbatim.

**3. The fractional half**
- **Meaning of `1 / r`.** Because the theorem holds for every interpretation of `Div`, it holds in particular when `1 / r` is the true reciprocal and `M^(1/r)` is the true r-th root. The book itself says "Similarly," which is the instance `p := 1/r`, so the second conjunct is faithful.
- **"Integral or fractional."** The book's heading claims one law for "any power, integral or fractional." A single statement over all of `E` covers both kinds, and both appear when `E` is instantiated to the reals.
- **The case `r = 0`.** The book implicitly takes `r ≠ 0`. A statement that remains true without that side condition is stronger than the book's, not weaker.

I concede no point. The statement is faithful, general and checked by Lean, so the pull request should merge.

## supervisor
**MERGE**

Lean accepts the final code, and its conclusion is the book's equality `log_a (M^p) = p · log_a M` for a valid base and a positive `M`. Every hypothesis holds for positive reals under real powers, and the defender's `Nat` model with powers of 2 shows the hypotheses are satisfiable without degeneracy. None of the critic's points stands: Art. 206 itself presupposes the index law and the existence and uniqueness of logarithms from Art. 199, and the `1/r` conjunct holds for every interpretation of `Div`, including the true reciprocal.
