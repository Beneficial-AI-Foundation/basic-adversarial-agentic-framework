## issue
Issue #514. To find the remainder when any rational integral function of x is divided by x − a (Art. 514)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XXXIV (Miscellaneous Theorems and Examples), Art. 514.
The book prints the following text.
[From Art. 535, p. 451] Let p_0 x^n + p_1 x^(n−1) + p_2 x^(n−2) + ...... + p_(n−1) x + p_n be a rational integral function of x of n dimensions, and let us denote it by f(x);
Let f(x) denote any rational integral function of x; divide f(x) by x − a until a remainder is obtained which does not involve x; let Q be the quotient, and R the remainder; then f(x) = Q(x − a) + R.
R = f(a).
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_514.

## prover
/-- A rational integral function of `x` is represented by the list of its
coefficients `[c₀, c₁, …, cₙ]`, in ascending powers of `x`, and is evaluated
as `c₀ + c₁ x + ⋯ + cₙ xⁿ`. -/
def evalPoly : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

/-- Division by `x - a` always yields a quotient `Q` and a remainder that is free of `x`,
and that remainder is `f(a)`. -/
theorem exists_quot (f : List Int) (a : Int) :
    ∃ Q : List Int, ∀ x, evalPoly f x = evalPoly Q x * (x - a) + evalPoly f a := by
  induction f with
  | nil => exact ⟨[], fun x => by simp [evalPoly]⟩
  | cons c cs ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨evalPoly cs a :: Q, fun x => ?_⟩
    simp only [evalPoly]
    rw [hQ x]
    generalize evalPoly Q x = q
    generalize evalPoly cs a = r
    have h1 : (r + x * q) * (x - a) = r * x - r * a + x * (q * (x - a)) := by
      rw [Int.add_mul, Int.mul_sub r x a, Int.mul_assoc x q (x - a)]
    have h2 : x * (q * (x - a) + r) = x * (q * (x - a)) + r * x := by
      rw [Int.mul_add, Int.mul_comm x r]
    have h3 : a * r = r * a := Int.mul_comm a r
    rw [h1, h2, h3]
    omega

/-- Remainder theorem (Hall and Knight, Art. 514).
Let `f(x)` be any rational integral function of `x`.
Dividing `f(x)` by `x - a` gives a quotient `Q` and a remainder `R` free of `x`,
with `f(x) = Q(x - a) + R`.
Whenever such an identity holds, `R = f(a)`. -/
theorem hk_art_514 (f : List Int) (a : Int) :
    (∃ Q : List Int, ∀ x, evalPoly f x = evalPoly Q x * (x - a) + evalPoly f a) ∧
    (∀ (Q : List Int) (R : Int),
      (∀ x, evalPoly f x = evalPoly Q x * (x - a) + R) → R = evalPoly f a) := by
  refine ⟨exists_quot f a, ?_⟩
  intro Q R h
  have h' := h a
  rw [Int.sub_self, Int.mul_zero, Int.zero_add] at h'
  exact h'.symm

## lean
Lean accepts the code.

## challenger
OBJECTION: The theorem is proved only for integer coefficients, an integer a and integer x, since `evalPoly : List Int → Int → Int`. The book's "rational integral function" has arbitrary numerical coefficients p_0, …, p_n, and a is an arbitrary number, so the statement is strictly weaker than the prose. For example, f(x) = x²/2 + 1 divided by x − 1/3 is not covered. The prover should either generalize the coefficient and value type (e.g. a type with the needed ring operations as hypotheses, or a rational type) or justify why the integer case faithfully represents Art. 514.

## prover
-- Repair: the objection holds. Coefficients, `a` and `x` now range over any type `α` that
-- satisfies the commutative ring laws in `PolyRing`. The rationals, the reals and the integers
-- are such types, so `f(x) = x²/2 + 1` divided by `x - 1/3` is now covered.

universe u

/-- The laws of a commutative ring with subtraction, used as hypotheses on the number type
of the coefficients. -/
class PolyRing (α : Type u) extends Add α, Mul α, Neg α, Sub α where
  zero : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + zero = a
  add_neg : ∀ a : α, a + -a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_add : ∀ a b c : α, a * (b + c) = a * b + a * c
  mul_zero : ∀ a : α, a * zero = zero
  sub_eq : ∀ a b : α, a - b = a + -b

/-- A rational integral function of `x` is represented by the list of its
coefficients `[c₀, c₁, …, cₙ]`, in ascending powers of `x`, and is evaluated
as `c₀ + c₁ x + ⋯ + cₙ xⁿ`. -/
def evalPoly {α : Type u} [PolyRing α] : List α → α → α
  | [], _ => PolyRing.zero
  | c :: cs, x => c + x * evalPoly cs x

theorem poly_key {α : Type u} [PolyRing α] (r x a : α) :
    r * (x - a) + a * r = r * x := by
  rw [PolyRing.sub_eq x a, PolyRing.mul_add r x (-a), PolyRing.add_assoc (r * x) (r * -a) (a * r),
    PolyRing.mul_comm a r, ← PolyRing.mul_add r (-a) a, PolyRing.add_comm (-a) a,
    PolyRing.add_neg a, PolyRing.mul_zero r, PolyRing.add_zero (r * x)]

theorem poly_shuffle {α : Type u} [PolyRing α] (A B C D : α) :
    (A + B) + (C + D) = C + (B + (A + D)) := by
  rw [PolyRing.add_comm A B, PolyRing.add_assoc B A (C + D), ← PolyRing.add_assoc A C D,
    PolyRing.add_comm A C, PolyRing.add_assoc C A D, ← PolyRing.add_assoc B C (A + D),
    PolyRing.add_comm B C, PolyRing.add_assoc C B (A + D)]

/-- Division by `x - a` always yields a quotient `Q` and a remainder that is free of `x`,
and that remainder is `f(a)`. -/
theorem exists_quot {α : Type u} [PolyRing α] (f : List α) (a : α) :
    ∃ Q : List α, ∀ x, evalPoly f x = evalPoly Q x * (x - a) + evalPoly f a := by
  induction f with
  | nil =>
    refine ⟨[], fun x => ?_⟩
    simp only [evalPoly]
    rw [PolyRing.mul_comm PolyRing.zero (x - a), PolyRing.mul_zero (x - a),
      PolyRing.add_zero (PolyRing.zero : α)]
  | cons c cs ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨evalPoly cs a :: Q, fun x => ?_⟩
    simp only [evalPoly]
    rw [hQ x]
    generalize evalPoly Q x = q
    generalize evalPoly cs a = r
    rw [PolyRing.mul_add x (q * (x - a)) r, PolyRing.mul_comm x r,
      PolyRing.mul_comm (r + x * q) (x - a), PolyRing.mul_add (x - a) r (x * q),
      PolyRing.mul_comm (x - a) r, PolyRing.mul_comm (x - a) (x * q),
      PolyRing.mul_assoc x q (x - a),
      poly_shuffle (r * (x - a)) (x * (q * (x - a))) c (a * r), poly_key r x a]

/-- Remainder theorem (Hall and Knight, Art. 514).
Let `f(x)` be any rational integral function of `x`, with coefficients and the number `a`
taken in any commutative ring (for example the rationals or the reals).
Dividing `f(x)` by `x - a` gives a quotient `Q` and a remainder `R` free of `x`,
with `f(x) = Q(x - a) + R`.
Whenever such an identity holds, `R = f(a)`. -/
theorem hk_art_514 {α : Type u} [PolyRing α] (f : List α) (a : α) :
    (∃ Q : List α, ∀ x, evalPoly f x = evalPoly Q x * (x - a) + evalPoly f a) ∧
    (∀ (Q : List α) (R : α),
      (∀ x, evalPoly f x = evalPoly Q x * (x - a) + R) → R = evalPoly f a) := by
  refine ⟨exists_quot f a, ?_⟩
  intro Q R h
  have h' := h a
  rw [PolyRing.sub_eq a a, PolyRing.add_neg a, PolyRing.mul_zero (evalPoly Q a),
    PolyRing.add_comm PolyRing.zero R, PolyRing.add_zero R] at h'
  exact h'.symm

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The generalization answers my earlier objection. `PolyRing` asks only for the commutative ring laws (no unit is needed), and it is not vacuous, since the integers satisfy it. Polynomials with coefficients, `a` and `x` in any such type are now covered. The first conjunct gives a polynomial quotient `Q` with `f(x) = Q(x)(x − a) + f(a)` for all `x`. The second conjunct shows that any remainder `R` free of `x` in such an identity equals `f(a)`. Together they state exactly the prose of Art. 514, and Lean accepts the proof.

## critic
**Position: do not merge.**

1. **The generalization that answers the challenger is asserted, not shown.** The objection was that integer coefficients cannot express f(x) = x²/2 + 1 divided by x − 1/3.
   - The repair replaces `Int` with a user-defined class `PolyRing`, but the code gives no instance of it: not for the rationals, not for the reals, not even for `Int`.
   - "The rationals, the reals and the integers are such types" appears only in comments. The checker never confirms that any concrete number type satisfies the ten hand-written axioms, or that its `zero` field matches that type's actual `0`.
   - The challenger accepted "it is not vacuous, since the integers satisfy it" without that fact appearing anywhere in the checked code.
   - The very example raised in the objection (x²/2 + 1, a = 1/3) is never instantiated. The rationals are the case Art. 514 calls for. Showing them would require a `Rat` type and an instance proof, and neither is supplied.
   - As written, the theorem is proved for an abstract class with no certified inhabitant relevant to the book. The prover replaced one gap (integers only) with another (no stated case at all). The challenger's "NO OBJECTION" rests on this unchecked claim.

2. **The existence half is weaker than the book's division process.** The book says to divide f(x) by x − a until the remainder does not involve x, giving a quotient Q of the polynomial p₀xⁿ + … + pₙ of n dimensions.
   - The first conjunct has no degree or structure for Q. It does not say that Q has n − 1 dimensions or that its leading coefficient is p₀.
   - It also fixes the remainder as `evalPoly f a` in the existence statement. The remainder is defined to be f(a) rather than obtained from the division, so this conjunct assumes the article's conclusion instead of modelling the division.
   - The only part that matches the prose is the second conjunct. That conjunct is a one-line substitution x := a. The statement is therefore partly circular, and its content is thinner than the challenger's summary ("together they state exactly the prose") suggests.

3. **The representation departs from the book's object without justification.** The book's f(x) is p₀xⁿ + p₁xⁿ⁻¹ + … + pₙ, written in descending powers with a stated dimension n.
   - The code uses an ascending coefficient list `[c₀, …, cₙ]` with no link to the pᵢ.
   - It does not require a nonzero leading coefficient, so a "function of n dimensions" is not represented.
   - It evaluates with a custom `PolyRing.zero` that is not tied to the type's own `0` or `OfNat` literal.
   - No lemma connects `evalPoly` to the book's expression for any concrete type. The fidelity of the main theorem to Art. 514 therefore rests on the reader trusting the docstrings rather than on anything Lean checked.

## defender
**Position: merge.**

1. **Missing instances.** The theorem is quantified over every `PolyRing` instance, so it holds for any type that meets ten standard, inspectable ring laws, including ℤ, ℚ and ℝ. Supplying an instance is a separate task that cannot weaken what was proved, and the `zero` worry fails because `add_comm` and `add_zero` force uniqueness (z = z + z′ = z′ + z = z′), so any instance's `zero` must be the type's real 0.

2. **The existence half.** The two conjuncts are logically independent: the first says division by x − a always leaves an x-free remainder (non-trivial, proved by induction via synthetic division), and the second says any such remainder equals f(a), assuming nothing from the first. This is not circular, and Art. 514 states only R = f(a) and never claims anything about Q's degree or leading coefficient, so omitting those adds no gap.

3. **The representation.** Ascending versus descending order is notation: the book's p₀xⁿ + … + pₙ is the list `[pₙ, …, p₀]`, and `evalPoly` is literally Horner's form c₀ + x(c₁ + x(…)), which is that sum by distributivity. Dropping the nonzero-leading-coefficient condition makes the theorem strictly more general, since every polynomial "of n dimensions" is one of the lists covered, and the `zero` concern is already settled by uniqueness in point 1.

## supervisor
**MERGE**

Lean accepts the final code, and the remainder theorem is true. The statement is faithful to Art. 514: it quantifies over every type obeying the commutative ring laws, which covers rational and real coefficients, and it gives both that division by x − a always leaves a quotient Q with f(x) = Q(x)(x − a) + f(a) and that any x-free remainder R equals f(a). None of the critic's points stands: a missing instance cannot weaken a universally quantified theorem, the two conjuncts are independent rather than circular, and the ascending coefficient list without a degree condition is only a notational choice that makes the result more general.
