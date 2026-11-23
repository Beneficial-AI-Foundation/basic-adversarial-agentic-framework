## issue
Issue #65. Art. 65, Harmonical Progression. Theorems connected with the Progressions
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter VI (Harmonical Progression. Theorems connected with the Progressions), Art. 65.
The book prints the following text.
53. DEFINITION. When three quantities are in Geometrical Progression the middle one is called the geometric mean between the other two.
If A, G, H be the arithmetic, geometric, and harmonic means between a and b, we have proved A = (a + b)/2 ......(1). G = √(ab) ......(2). H = 2ab/(a + b) ......(3).
AH = ((a + b)/2) . (2ab/(a + b)) = ab = G^2; that is, G is the geometric mean between A and H.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_65.

## prover
/-- Hall and Knight, Higher Algebra, Art. 65. Let `A`, `G`, `H` be the arithmetic, geometric
and harmonic means between `a` and `b`. Then `A * H = G ^ 2`, so `G` is the geometric mean
between `A` and `H`.

The core library has no real numbers, so the quantities are integers. Each mean is given by
its defining equation with the division cleared:
* `2 * A = a + b` stands for `A = (a + b) / 2`,
* `G * G = a * b` stands for `G = √(ab)`,
* `H * (a + b) = 2 * a * b` stands for `H = 2ab / (a + b)`, which needs `a + b ≠ 0`.

The conclusion `A * H = G * G` is the book's `AH = ab = G²`. -/
theorem hk_art_65 (a b A G H : Int) (hs : a + b ≠ 0)
    (hA : 2 * A = a + b) (hH : H * (a + b) = 2 * a * b) (hG : G * G = a * b) :
    A * H = G * G := by
  rw [hG]
  have h2 : (2 : Int) * (a + b) ≠ 0 := Int.mul_ne_zero (by decide) hs
  apply Int.eq_of_mul_eq_mul_left h2
  have h3 : 2 * (a + b) * (A * H) = (2 * A) * (H * (a + b)) := by
    simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  rw [h3, hA, hH]
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]

## lean
Lean accepts the code.

## challenger
OBJECTION: Over `Int`, the hypotheses can only be satisfied when `a + b` is even, `a * b` is a perfect square, and `a + b` divides `2 * a * b`. For example, `a = 1, b = 2` has no integer `A`, and `a = 1, b = 3` has no integer `G`, so the theorem says nothing about almost every pair of quantities. The book's result is about arbitrary positive quantities with `A = (a+b)/2`, `G = √(ab)` and `H = 2ab/(a+b)` as real or at least rational numbers. This integer statement is a strictly weaker special case, not the article's claim. It should be stated over a domain where the means always exist, such as `Rat`, or over an abstract commutative ring or field carrying the same defining equations, so that it covers general `a` and `b`.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The revised statement answers my earlier objection. It is generic over any type with commutative, associative multiplication in which 2 can be cancelled, so it covers ℚ, ℝ and any field of characteristic ≠ 2, where the three means exist for general `a` and `b`. The hypotheses are not vacuous, since `Int` and `Rat` satisfy them. The cleared-denominator equations are equivalent to the book's definitions under `a + b ≠ 0`. The conclusion `A * H = G * G` is exactly the book's `AH = ab = G²`. The `hs` hypothesis goes unused, and `G` may be either square root, but neither narrows the claim, so I cannot defend a further objection.

## critic
The pull request should not merge, for three reasons.

1. **The final statement no longer expresses the article's content.**
   - The binder `[Add α]` comes with no laws at all, so `+` can be any binary operation.
   - `[OfNat α 2]` makes `2` an arbitrary constant. Nothing ties it to `1 + 1`. The only property assumed is that `2` can be cancelled.
   - Once you write `s` for `a + b` and `c` for `2`, the theorem says: if `c*A = s`, `H*s = c*a*b` and `G*G = a*b`, then `A*H = G*G`. That is a three-line rewrite about uninterpreted symbols.
   - "Arithmetic mean" and "harmonic mean" carry no meaning here, because neither the halving nor the sum is constrained.
   - The issue asks for the result about the A.M., G.M. and H.M. of two quantities. What we have is an abstraction in which those notions cannot even be stated.
   - The Int version at least used the real `+` and `2`. The revision fixed the challenger's narrowness complaint by giving up any connection to the means.

2. **The prover's answer to the objection rests on claims nobody checked.**
   - The reply says the theorem "covers ℚ, ℝ, or any field of characteristic ≠ 2."
   - This project uses the core library only, which has no `ℝ` and no field class. No instantiation is given, not even for `Int` or `Rat`.
   - No `example` discharges `mul_comm`, `mul_assoc` and `two_cancel` for a concrete type. So the claim that the theorem specializes to the book's setting, where `A`, `G` and `H` exist for general `a` and `b`, is asserted but not proved.
   - The challenger's objection was precisely that the means must exist for general `a` and `b`. The prover did not demonstrate that. The challenger then withdrew the objection on the same unverified assertion that "Int and Rat satisfy them."

3. **The statement contains misleading parts.**
   - The hypothesis `hs : a + b ≠ 0` is never used, and Lean's unused-variable linter will flag it. The `[OfNat α 0]` binder exists only to support it.
   - The docstring says the `H` equation "needs `a + b ≠ 0`." The proof shows the theorem does not depend on it, so the documentation misdescribes what is proved.
   - `G` may be either square root of `ab`. The book's `G = √(ab)` is the positive mean of positive quantities.
   - No positivity hypothesis on `a` and `b` appears, even though the book's means are defined for positive quantities.
   - A merged `hk_art_65` should say exactly what it proves. This one carries decorative hypotheses and comments that overstate how closely it follows the source.

## defender
1. **The theorem still expresses the article's content.** The article proves the identity `AH = ab = G²` from the three defining equations, and that is all this statement asserts. Because it is generic in `+` and `2`, it holds in every intended instance where `+` and `2` are the real ones (take `α := Int`, or `Rat` where available), so the book's claim is a direct specialization rather than something lost.

2. **The specialization needs no further proof.** For `Int`, the side conditions are discharged by `Int.mul_comm`, `Int.mul_assoc` and `Int.eq_of_mul_eq_mul_left (by decide)`, exactly as in the first accepted version, and any field of characteristic ≠ 2 satisfies them by its axioms. The missing `example` affects documentation only, not the correctness or fidelity of the statement. In such a field, `A = (a+b)/2` always exists and `H = 2ab/(a+b)` exists whenever `a + b ≠ 0`, so the challenger's existence concern is met by the general statement itself.

3. **These parts are accurate, not misleading.**
   - `hs` encodes the book's own domain condition for `H = 2ab/(a+b)`, and the docstring says only that the book's definition needs it, which is true. An extra hypothesis can only weaken the theorem, and an unused-variable lint is a warning, not a merge blocker.
   - Allowing either square root `G` and dropping positivity are strict generalizations. The book's case of positive quantities with the positive root is a special instance, so the claim is never overstated.

## supervisor
**MERGE**

Lean accepts the final code. The statement is a sound generalization: taking α to be ℚ, ℝ or any field of characteristic ≠ 2, with the real `+` and `2`, the hypotheses become exactly the book's defining equations with denominators cleared, and the conclusion is the book's `AH = G²`. None of the critic's points stands as a defect: abstracting over `+` and `2`, the unused but faithful hypothesis `a + b ≠ 0`, allowing either square root and dropping positivity all only weaken the assumptions, so the book's case remains a direct instance.
