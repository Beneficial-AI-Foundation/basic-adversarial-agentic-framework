## issue
Issue #5141. Cor. to Art. 514
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XXXIV (Miscellaneous Theorems and Examples), Art. 514, Cor..
The book prints the following text.
[From Art. 535, p. 451] Let p_0 x^n + p_1 x^(n−1) + p_2 x^(n−2) + ...... + p_(n−1) x + p_n be a rational integral function of x of n dimensions, and let us denote it by f(x);
Let f(x) denote any rational integral function of x; divide f(x) by x − a until a remainder is obtained which does not involve x; let Q be the quotient, and R the remainder; then f(x) = Q(x − a) + R. [Result of Art. 514] R = f(a).
COR. If f(x) is exactly divisible by x − a, then R = 0, that is f(a) = 0; hence if a rational integral function of x vanishes when x = a, it is divisible by x − a.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_514_cor.

## prover
/-- Cor. to Art. 514 (Hall & Knight, *Higher Algebra*): if a rational integral function
`f(x) = p_0 x^n + p_1 x^(n-1) + ... + p_n` vanishes when `x = a`, then `f(x)` is divisible
by `x - a`. That is, there is a rational integral function `Q(x)` with `f(x) = (x - a) Q(x)`
for every `x`.

Encoding: a polynomial is its list of coefficients, lowest degree first. So `[c₀, c₁, …]`
stands for `c₀ + c₁ x + …`. Core Lean has no field of rationals or reals, so the
coefficients and the variable range over `Int`. The quotient is also given by integer
coefficients. -/
def evalPoly : List Int → Int → Int
  | [], _ => 0
  | c :: cs, x => c + x * evalPoly cs x

/-- Art. 514: dividing `f(x)` by `x - a` gives `f(x) = Q(x)(x - a) + R`, with `R` free of `x`. -/
theorem hk_art_514_div (cs : List Int) (a : Int) :
    ∃ qs : List Int, ∃ r : Int, ∀ x, evalPoly cs x = (x - a) * evalPoly qs x + r := by
  induction cs with
  | nil => exact ⟨[], 0, fun x => by simp [evalPoly]⟩
  | cons c cs ih =>
    obtain ⟨qs, r, h⟩ := ih
    refine ⟨r :: qs, c + a * r, fun x => ?_⟩
    have hx := h x
    simp only [evalPoly]
    rw [hx]
    generalize evalPoly qs x = Q
    have h0 : x * ((x - a) * Q + r) = x * ((x - a) * Q) + x * r := Int.mul_add _ _ _
    have h1 : x * ((x - a) * Q) = (x - a) * (x * Q) := Int.mul_left_comm _ _ _
    have h2 : (x - a) * (r + x * Q) = (x - a) * r + (x - a) * (x * Q) := Int.mul_add _ _ _
    have h3 : (x - a) * r = x * r - a * r := Int.sub_mul _ _ _
    omega

/-- Cor. to Art. 514: if a rational integral function `f` vanishes when `x = a`, it is
divisible by `x - a`. There is a rational integral function `Q` with `f(x) = (x - a) Q(x)`
identically. -/
theorem hk_art_514_cor (f : List Int) (a : Int) (hf : evalPoly f a = 0) :
    ∃ qs : List Int, ∀ x, evalPoly f x = (x - a) * evalPoly qs x := by
  obtain ⟨qs, r, h⟩ := hk_art_514_div f a
  have hr : r = 0 := by
    have := h a
    rw [Int.sub_self, Int.zero_mul, Int.zero_add] at this
    omega
  exact ⟨qs, fun x => by rw [h x, hr, Int.add_zero]⟩

## lean
Lean accepts the code.

## challenger
OBJECTION: The theorem fixes both the coefficients and the variable to `Int`, so it proves only a special case. The book's "rational integral function" allows arbitrary (rational, real) coefficients and an arbitrary value `a`; for example, `f(x) = 2x − 1` vanishing at `a = 1/2` cannot even be stated here. The claim that core Lean lacks a suitable number type does not justify this: the statement could be made generic over any type with commutative-ring operations, or use `Rat`. The formalization also drops the first half of the corollary, that exact divisibility by `x − a` gives `f(a) = 0`, which the prose states explicitly.

## prover
-- The objection holds, and this revision fixes both points it raises.
-- 1. The statement no longer fixes `Int`. It works over any type `α` with commutative-ring
--    operations, given by the class `CRing` below. Core Lean has no algebraic hierarchy, so the
--    class is defined here. Rationals and reals are instances, so `f(x) = 2x − 1` with
--    `a = 1/2` can now be stated.
-- 2. The theorem now states both halves of the corollary as an equivalence. If `f` is exactly
--    divisible by `x − a`, then `f(a) = 0`. If `f(a) = 0`, then `f` is divisible by `x − a`.

universe u

/-- Commutative ring operations and axioms: the coefficient domain of a rational integral function. -/
class CRing (α : Type u) extends Add α, Mul α, Neg α where
  zero : α
  one : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c

namespace CRing

variable {α : Type u} [CRing α]

instance instSub : Sub α := ⟨fun a b => a + -b⟩

theorem sub_eq (a b : α) : a - b = a + -b := rfl

theorem add_zero (a : α) : a + CRing.zero = a := by
  rw [CRing.add_comm, CRing.zero_add]

theorem add_neg (a : α) : a + -a = CRing.zero := by
  rw [CRing.add_comm, CRing.neg_add]

theorem self_eq (t : α) (h : t + t = t) : t = CRing.zero :=
  calc t = CRing.zero + t := (CRing.zero_add t).symm
    _ = (-t + t) + t := by rw [CRing.neg_add]
    _ = -t + (t + t) := CRing.add_assoc _ _ _
    _ = -t + t := by rw [h]
    _ = CRing.zero := CRing.neg_add t

theorem mul_zero (a : α) : a * CRing.zero = CRing.zero :=
  CRing.self_eq _ (by rw [← CRing.left_distrib, CRing.zero_add])

theorem zero_mul (a : α) : CRing.zero * a = CRing.zero := by
  rw [CRing.mul_comm, CRing.mul_zero]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [CRing.mul_comm, CRing.left_distrib, CRing.mul_comm c a, CRing.mul_comm c b]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← CRing.mul_assoc a b c, CRing.mul_comm a b, CRing.mul_assoc b a c]

theorem rearr (c P X N A : α) (h : N + A = CRing.zero) :
    c + (P + X) = ((X + N) + P) + (c + A) := by
  rw [CRing.add_assoc X N P, CRing.add_comm N P, ← CRing.add_assoc X P N,
    CRing.add_assoc (X + P) N (c + A), CRing.add_comm c A, ← CRing.add_assoc N A c, h,
    CRing.zero_add, CRing.add_comm X P, CRing.add_comm (P + X) c]

theorem step (c x a Q r : α) :
    c + x * ((x + -a) * Q + r) = (x + -a) * (r + x * Q) + (c + a * r) := by
  rw [CRing.left_distrib x ((x + -a) * Q) r, CRing.mul_left_comm x (x + -a) Q,
    CRing.left_distrib (x + -a) r (x * Q), CRing.right_distrib x (-a) r]
  exact CRing.rearr c ((x + -a) * (x * Q)) (x * r) ((-a) * r) (a * r)
    (by rw [← CRing.right_distrib, CRing.neg_add, CRing.zero_mul])

end CRing

/-- A rational integral function is given by its list of coefficients, lowest degree first.
`[c₀, c₁, …]` stands for `c₀ + c₁ x + …`. -/
def evalPoly {α : Type u} [CRing α] : List α → α → α
  | [], _ => CRing.zero
  | c :: cs, x => c + x * evalPoly cs x

theorem evalPoly_nil {α : Type u} [CRing α] (x : α) :
    evalPoly ([] : List α) x = CRing.zero := rfl

theorem evalPoly_cons {α : Type u} [CRing α] (c : α) (cs : List α) (x : α) :
    evalPoly (c :: cs) x = c + x * evalPoly cs x := rfl

/-- Art. 514: dividing `f(x)` by `x - a` gives `f(x) = Q(x)(x - a) + R`, with `R` free of `x`. -/
theorem hk_art_514_div {α : Type u} [CRing α] (cs : List α) (a : α) :
    ∃ qs : List α, ∃ r : α, ∀ x, evalPoly cs x = (x - a) * evalPoly qs x + r := by
  induction cs with
  | nil =>
    refine ⟨[], CRing.zero, fun x => ?_⟩
    rw [evalPoly_nil, evalPoly_nil, CRing.mul_zero, CRing.zero_add]
  | cons c cs ih =>
    obtain ⟨qs, r, h⟩ := ih
    refine ⟨r :: qs, c + a * r, fun x => ?_⟩
    rw [evalPoly_cons c cs x, evalPoly_cons r qs x, h x, CRing.sub_eq x a]
    exact CRing.step c x a (evalPoly qs x) r

/-- Cor. to Art. 514 (Hall & Knight, *Higher Algebra*), over any commutative ring of
coefficients. If the rational integral function `f(x)` is exactly divisible by `x − a`, that
is `f(x) = (x − a) Q(x)` identically for some rational integral `Q`, then `f(a) = 0`.
Conversely, if `f` vanishes when `x = a`, then `f` is divisible by `x − a`. -/
theorem hk_art_514_cor {α : Type u} [CRing α] (f : List α) (a : α) :
    (∃ qs : List α, ∀ x, evalPoly f x = (x - a) * evalPoly qs x) ↔
      evalPoly f a = CRing.zero := by
  constructor
  · intro ⟨qs, h⟩
    rw [h a, CRing.sub_eq, CRing.add_neg, CRing.zero_mul]
  · intro hf
    obtain ⟨qs, r, h⟩ := hk_art_514_div f a
    have hr : r = CRing.zero := by
      have h1 := h a
      rw [hf, CRing.sub_eq, CRing.add_neg, CRing.zero_mul, CRing.zero_add] at h1
      exact h1.symm
    exact ⟨qs, fun x => by rw [h x, hr, CRing.add_zero]⟩

## lean
The Lean check failed. Lean rejects the code. <stdin>:90:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  evalPoly [] ?x
in the target expression
  CRing.zero = (x - a) * CRing.zero + CRing.zero

case nil
α : Type u
inst✝ : CRing α
a x : α
⊢ CRing.zero = (x - a) * CRing.zero + CRing.zero
'hk_art_514_cor' depends on axioms: [sorryAx]


## challenger
OBJECTION: The Lean check failed, so this revision proves nothing. In the `nil` case of `hk_art_514_div`, the first `rw [evalPoly_nil]` already unfolds both occurrences of `evalPoly []`. The second `evalPoly_nil` then finds no match, and the error fires at line 90. As a result, `hk_art_514_cor` depends on `sorryAx`, and the main theorem is not established.

## prover
-- The objection holds. In the `nil` case of `hk_art_514_div`, the first `rw [evalPoly_nil]` already
-- rewrites both occurrences of `evalPoly []`, so the second rewrite found nothing and failed.
-- This revision removes the redundant rewrite and changes nothing else.
--
-- The earlier objection is still answered as follows.
-- 1. The statement works over any type `α` with commutative-ring operations, given by the class
--    `CRing` below. Core Lean has no algebraic hierarchy, so the class is defined here.
--    Rationals and reals are instances, so `f(x) = 2x − 1` with `a = 1/2` can be stated.
-- 2. The theorem states both halves of the corollary as an equivalence. If `f` is exactly
--    divisible by `x − a`, then `f(a) = 0`. If `f(a) = 0`, then `f` is divisible by `x − a`.

universe u

/-- Commutative ring operations and axioms: the coefficient domain of a rational integral function. -/
class CRing (α : Type u) extends Add α, Mul α, Neg α where
  zero : α
  one : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c

namespace CRing

variable {α : Type u} [CRing α]

instance instSub : Sub α := ⟨fun a b => a + -b⟩

theorem sub_eq (a b : α) : a - b = a + -b := rfl

theorem add_zero (a : α) : a + CRing.zero = a := by
  rw [CRing.add_comm, CRing.zero_add]

theorem add_neg (a : α) : a + -a = CRing.zero := by
  rw [CRing.add_comm, CRing.neg_add]

theorem self_eq (t : α) (h : t + t = t) : t = CRing.zero :=
  calc t = CRing.zero + t := (CRing.zero_add t).symm
    _ = (-t + t) + t := by rw [CRing.neg_add]
    _ = -t + (t + t) := CRing.add_assoc _ _ _
    _ = -t + t := by rw [h]
    _ = CRing.zero := CRing.neg_add t

theorem mul_zero (a : α) : a * CRing.zero = CRing.zero :=
  CRing.self_eq _ (by rw [← CRing.left_distrib, CRing.zero_add])

theorem zero_mul (a : α) : CRing.zero * a = CRing.zero := by
  rw [CRing.mul_comm, CRing.mul_zero]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [CRing.mul_comm, CRing.left_distrib, CRing.mul_comm c a, CRing.mul_comm c b]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← CRing.mul_assoc a b c, CRing.mul_comm a b, CRing.mul_assoc b a c]

theorem rearr (c P X N A : α) (h : N + A = CRing.zero) :
    c + (P + X) = ((X + N) + P) + (c + A) := by
  rw [CRing.add_assoc X N P, CRing.add_comm N P, ← CRing.add_assoc X P N,
    CRing.add_assoc (X + P) N (c + A), CRing.add_comm c A, ← CRing.add_assoc N A c, h,
    CRing.zero_add, CRing.add_comm X P, CRing.add_comm (P + X) c]

theorem step (c x a Q r : α) :
    c + x * ((x + -a) * Q + r) = (x + -a) * (r + x * Q) + (c + a * r) := by
  rw [CRing.left_distrib x ((x + -a) * Q) r, CRing.mul_left_comm x (x + -a) Q,
    CRing.left_distrib (x + -a) r (x * Q), CRing.right_distrib x (-a) r]
  exact CRing.rearr c ((x + -a) * (x * Q)) (x * r) ((-a) * r) (a * r)
    (by rw [← CRing.right_distrib, CRing.neg_add, CRing.zero_mul])

end CRing

/-- A rational integral function is given by its list of coefficients, lowest degree first.
`[c₀, c₁, …]` stands for `c₀ + c₁ x + …`. -/
def evalPoly {α : Type u} [CRing α] : List α → α → α
  | [], _ => CRing.zero
  | c :: cs, x => c + x * evalPoly cs x

theorem evalPoly_nil {α : Type u} [CRing α] (x : α) :
    evalPoly ([] : List α) x = CRing.zero := rfl

theorem evalPoly_cons {α : Type u} [CRing α] (c : α) (cs : List α) (x : α) :
    evalPoly (c :: cs) x = c + x * evalPoly cs x := rfl

/-- Art. 514: dividing `f(x)` by `x - a` gives `f(x) = Q(x)(x - a) + R`, with `R` free of `x`. -/
theorem hk_art_514_div {α : Type u} [CRing α] (cs : List α) (a : α) :
    ∃ qs : List α, ∃ r : α, ∀ x, evalPoly cs x = (x - a) * evalPoly qs x + r := by
  induction cs with
  | nil =>
    refine ⟨[], CRing.zero, fun x => ?_⟩
    rw [evalPoly_nil, CRing.mul_zero, CRing.zero_add]
  | cons c cs ih =>
    obtain ⟨qs, r, h⟩ := ih
    refine ⟨r :: qs, c + a * r, fun x => ?_⟩
    rw [evalPoly_cons c cs x, evalPoly_cons r qs x, h x, CRing.sub_eq x a]
    exact CRing.step c x a (evalPoly qs x) r

/-- Cor. to Art. 514 (Hall & Knight, *Higher Algebra*), over any commutative ring of
coefficients. If the rational integral function `f(x)` is exactly divisible by `x − a`, that
is `f(x) = (x − a) Q(x)` identically for some rational integral `Q`, then `f(a) = 0`.
Conversely, if `f` vanishes when `x = a`, then `f` is divisible by `x − a`. -/
theorem hk_art_514_cor {α : Type u} [CRing α] (f : List α) (a : α) :
    (∃ qs : List α, ∀ x, evalPoly f x = (x - a) * evalPoly qs x) ↔
      evalPoly f a = CRing.zero := by
  constructor
  · intro ⟨qs, h⟩
    rw [h a, CRing.sub_eq, CRing.add_neg, CRing.zero_mul]
  · intro hf
    obtain ⟨qs, r, h⟩ := hk_art_514_div f a
    have hr : r = CRing.zero := by
      have h1 := h a
      rw [hf, CRing.sub_eq, CRing.add_neg, CRing.zero_mul, CRing.zero_add] at h1
      exact h1.symm
    exact ⟨qs, fun x => by rw [h x, hr, CRing.add_zero]⟩

## lean
Lean accepts the code.

## challenger
OBJECTION: "Exactly divisible by x − a" is encoded as pointwise equality of functions, `∀ x, evalPoly f x = (x - a) * evalPoly qs x`, not as an identity of polynomials. Once the statement is generalized to an arbitrary `CRing`, that is strictly weaker. Over a finite field such as ℤ/p, every function is a polynomial function, so the converse conclusion follows from `f(a) = 0` by interpolation alone and no longer expresses the factor theorem. Divisibility should be stated as equality of coefficient lists, for example `f` equals the coefficients of `(x − a)·Q` via a defined polynomial multiplication. Alternatively, the hypotheses must make the function identity imply the polynomial one, and the claim that `Rat` is a `CRing` instance should be backed by an actual instance.

## critic
**Recommendation: do not merge.** The final code compiles, but the theorem it proves is not the corollary in the issue, and the last objection has no answer.

1. **The challenger's last objection is unanswered, and it is correct.** "Exactly divisible by x − a" is encoded as `∃ qs, ∀ x, evalPoly f x = (x - a) * evalPoly qs x`, which is an identity of functions, not of polynomials.
   - Over Int this was harmless. Once the statement is generalized to an arbitrary `CRing`, it becomes too weak.
   - Over ℤ/p, every function is a polynomial function. Given `f(a) = 0`, a pointwise quotient exists trivially: set Q(x) = f(x)/(x − a) for x ≠ a, choose any value at a, then interpolate.
   - So the right-to-left direction no longer states the factor theorem.
   - The book's Q is the quotient produced by dividing f(x) by x − a, which is a polynomial identity. `hk_art_514_div` actually constructs such a quotient by synthetic division. The main theorem discards this and exports only the weaker pointwise statement.
   - The revision that introduced the generalization created this gap. The prover has not responded to it.

2. **The generality claim offered against the first objection is asserted, not delivered.** The prover says "Rationals and reals are instances, so `f(x) = 2x − 1` with `a = 1/2` can be stated." The file contains no instance at all: no `Int`, no `Rat`, nothing.
   - There is therefore no check that `CRing` is the intended structure, or even that the original Int result is recovered as a special case.
   - `x - a` in the theorem is the locally defined `CRing.instSub`, i.e. `a + -b`. It is not the carrier's own subtraction.
   - Applied to `Rat`, the statement would use a different `HSub` than a user writes. Bridging the two would need an unproved lemma.
   - The answer to the first objection, that the challenger's example "can now be stated", is unverified in the PR.

3. **The statement drifts from the issue's prose in ways that are not acknowledged.**
   - The issue frames the corollary on Art. 514's result that R = f(a). `hk_art_514_div` never states `r = evalPoly cs a`; that fact is only re-derived inside the corollary's proof.
   - The class carries `one`/`one_mul` but no `zero ≠ one`, so the trivial ring is admitted. The theorem's docstring silently replaces "rational integral function" (rational or real coefficients) with "any commutative ring". Point 1 shows that this replacement changes what the conclusion means.
   - Any of these could be fixed: define polynomial multiplication and state `f = mulPoly [-a, 1] qs`, or restrict to an infinite integral domain. Until then, the theorem named `hk_art_514_cor` does not faithfully state the book's corollary.

## defender
**Defender: the PR should merge.** The checked theorem is a true and faithful statement of the corollary, and nothing in the file needs a fix.

1. **Pointwise identity.** Hall & Knight treat a rational integral function as a function of x, and they define "f(x) = Q(x − a) + R" as an identity that holds for every value of x, so `∀ x, …` is the book's own notion of exact division. For the book's coefficient domains (rationals and reals, which are infinite integral domains), pointwise and coefficient identity coincide, so the ℤ/p behaviour concerns a case the book never considers and makes nothing about the book's case false.

2. **No instance in the file.** A theorem quantified over every lawful `CRing` needs no instance to be correct, and the remark about `Rat` is a comment rather than part of the checked statement. The original Int result is recovered without any bridging lemma, because `Int.sub m n` is defined as `m + -n`: the local `x - a` reduces to Int's own subtraction by `rfl`.

3. **Drift from the prose.** The issue asks for the corollary under the name `hk_art_514_cor`, and its proof derives R = f(a) exactly where that fact is needed, so `hk_art_514_div` is a helper that need not restate Art. 514 in full. Admitting the trivial ring only adds a case in which the theorem still holds, and the book's argument never uses 0 ≠ 1; the remaining drift objection repeats point 1.

## supervisor
**REVISE.** In the final, generic version, "exactly divisible by x − a" is encoded only as a pointwise identity. Over an arbitrary `CRing` such as ℤ/p, that no longer expresses the factor theorem, and the defender's appeal to infinite integral domains does not match the theorem's actual hypotheses. The prover should define polynomial multiplication and state the conclusion as an equality of coefficient lists, f = (x − a)·Q, using the quotient already built in `hk_art_514_div` (and state R = f(a) there), or else restrict to Int/Rat with real instances and their own subtraction, so the claimed special cases are actually checked.

## prover
-- The objection holds, and this revision repairs it.
-- 1. "Exactly divisible by x − a" is now an identity of polynomials, not of functions.
--    `mulLin a qs` is the coefficient list of (x − a)·Q, defined by polynomial multiplication.
--    The conclusion says that `f` and (x − a)·Q have the same coefficient in every degree.
--    `coeff` reads missing coefficients as zero, so trailing zeros do not matter.
--    Over ℤ/p this is still the factor theorem, not a statement about interpolated functions.
-- 2. The quotient is the one built by synthetic division in `hk_art_514_div`.
--    That theorem now also states R = f(a), which is Art. 514.
-- 3. Subtraction no longer appears in the statement; x − a is written as `x + -a`.
--    An actual `CRing Int` instance is given, and the Int case `hk_art_514_cor_int` is checked
--    with Int's own `0`. No `Rat` instance is claimed.

universe u

/-- Commutative ring operations and axioms: the coefficient domain of a rational integral function. -/
class CRing (α : Type u) extends Add α, Mul α, Neg α where
  zero : α
  one : α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c

namespace CRing

variable {α : Type u} [CRing α]

theorem add_zero (a : α) : a + CRing.zero = a := by
  rw [CRing.add_comm, CRing.zero_add]

theorem add_neg (a : α) : a + -a = CRing.zero := by
  rw [CRing.add_comm, CRing.neg_add]

theorem self_eq (t : α) (h : t + t = t) : t = CRing.zero :=
  calc t = CRing.zero + t := (CRing.zero_add t).symm
    _ = (-t + t) + t := by rw [CRing.neg_add]
    _ = -t + (t + t) := CRing.add_assoc _ _ _
    _ = -t + t := by rw [h]
    _ = CRing.zero := CRing.neg_add t

theorem mul_zero (a : α) : a * CRing.zero = CRing.zero :=
  CRing.self_eq _ (by rw [← CRing.left_distrib, CRing.zero_add])

theorem zero_mul (a : α) : CRing.zero * a = CRing.zero := by
  rw [CRing.mul_comm, CRing.mul_zero]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [CRing.mul_comm, CRing.left_distrib, CRing.mul_comm c a, CRing.mul_comm c b]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← CRing.mul_assoc a b c, CRing.mul_comm a b, CRing.mul_assoc b a c]

theorem rearr (c P X N A : α) (h : N + A = CRing.zero) :
    c + (P + X) = ((X + N) + P) + (c + A) := by
  rw [CRing.add_assoc X N P, CRing.add_comm N P, ← CRing.add_assoc X P N,
    CRing.add_assoc (X + P) N (c + A), CRing.add_comm c A, ← CRing.add_assoc N A c, h,
    CRing.zero_add, CRing.add_comm X P, CRing.add_comm (P + X) c]

theorem step (c x a Q r : α) :
    c + x * ((x + -a) * Q + r) = (x + -a) * (r + x * Q) + (c + a * r) := by
  rw [CRing.left_distrib x ((x + -a) * Q) r, CRing.mul_left_comm x (x + -a) Q,
    CRing.left_distrib (x + -a) r (x * Q), CRing.right_distrib x (-a) r]
  exact CRing.rearr c ((x + -a) * (x * Q)) (x * r) ((-a) * r) (a * r)
    (by rw [← CRing.right_distrib, CRing.neg_add, CRing.zero_mul])

end CRing

/-- The integers form a `CRing`. -/
instance : CRing Int where
  add := Int.add
  mul := Int.mul
  neg := Int.neg
  zero := 0
  one := 1
  add_assoc := fun a b c => Int.add_assoc a b c
  add_comm := fun a b => Int.add_comm a b
  zero_add := fun a => Int.zero_add a
  neg_add := fun a => by show -a + a = 0; omega
  mul_assoc := fun a b c => Int.mul_assoc a b c
  mul_comm := fun a b => Int.mul_comm a b
  one_mul := fun a => Int.one_mul a
  left_distrib := fun a b c => Int.mul_add a b c

section Poly

variable {α : Type u} [CRing α]

/-- A rational integral function is given by its list of coefficients, lowest degree first.
`[c₀, c₁, …]` stands for `c₀ + c₁ x + …`. -/
def evalPoly : List α → α → α
  | [], _ => CRing.zero
  | c :: cs, x => c + x * evalPoly cs x

/-- The coefficient of `x^n`. Missing coefficients are zero. -/
def coeff : List α → Nat → α
  | [], _ => CRing.zero
  | c :: _, 0 => c
  | _ :: cs, n + 1 => coeff cs n

/-- Add a constant `r` to a polynomial. -/
def addConst : α → List α → List α
  | r, [] => [r]
  | r, c :: cs => (r + c) :: cs

/-- Coefficients of the product `(x − a) · Q`. -/
def mulLin (a : α) : List α → List α
  | [] => []
  | q :: qs => ((-a) * q) :: addConst q (mulLin a qs)

theorem coeff_nil (n : Nat) : coeff ([] : List α) n = CRing.zero := by
  cases n <;> rfl

theorem eval_addConst (r : α) (p : List α) (x : α) :
    evalPoly (addConst r p) x = r + evalPoly p x := by
  cases p with
  | nil =>
    show r + x * CRing.zero = r + CRing.zero
    rw [CRing.mul_zero]
  | cons c cs =>
    show (r + c) + x * evalPoly cs x = r + (c + x * evalPoly cs x)
    rw [CRing.add_assoc]

theorem eval_mulLin (a : α) (qs : List α) (x : α) :
    evalPoly (mulLin a qs) x = (x + -a) * evalPoly qs x := by
  induction qs with
  | nil =>
    show CRing.zero = (x + -a) * CRing.zero
    rw [CRing.mul_zero]
  | cons q qs ih =>
    show (-a) * q + x * evalPoly (addConst q (mulLin a qs)) x
      = (x + -a) * (q + x * evalPoly qs x)
    rw [eval_addConst, ih, CRing.add_comm q ((x + -a) * evalPoly qs x),
      CRing.step ((-a) * q) x a (evalPoly qs x) q, ← CRing.right_distrib, CRing.neg_add,
      CRing.zero_mul, CRing.add_zero]

theorem eval_zero (f : List α) (x : α) :
    (∀ n, coeff f n = CRing.zero) → evalPoly f x = CRing.zero := by
  induction f with
  | nil => intro _; rfl
  | cons c cs ih =>
    intro h
    have h0 : c = CRing.zero := h 0
    have h1 := ih (fun n => h (n + 1))
    show c + x * evalPoly cs x = CRing.zero
    rw [h1, h0, CRing.mul_zero, CRing.zero_add]

theorem eval_congr (f g : List α) (x : α) :
    (∀ n, coeff f n = coeff g n) → evalPoly f x = evalPoly g x := by
  induction f generalizing g with
  | nil =>
    intro h
    exact (eval_zero g x (fun n => (h n).symm.trans (coeff_nil n))).symm
  | cons c cs ih =>
    intro h
    cases g with
    | nil => exact eval_zero (c :: cs) x (fun n => (h n).trans (coeff_nil n))
    | cons d ds =>
      have h0 : c = d := h 0
      have h1 : evalPoly cs x = evalPoly ds x := ih ds (fun n => h (n + 1))
      show c + x * evalPoly cs x = d + x * evalPoly ds x
      rw [h0, h1]

theorem coeff_addConst_zero (p : List α) (n : Nat) :
    coeff (addConst CRing.zero p) n = coeff p n := by
  cases p with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => exact (coeff_nil n).trans (coeff_nil (n + 1)).symm
  | cons c cs =>
    cases n with
    | zero => exact CRing.zero_add c
    | succ n => rfl

/-- Art. 514: dividing `f(x)` by `x − a` gives the polynomial identity `f(x) = (x − a) Q(x) + R`,
with remainder `R = f(a)`. The identity holds coefficient by coefficient. -/
theorem hk_art_514_div (cs : List α) (a : α) :
    ∃ qs : List α, ∀ n, coeff cs n = coeff (addConst (evalPoly cs a) (mulLin a qs)) n := by
  induction cs with
  | nil =>
    refine ⟨[], fun n => ?_⟩
    cases n with
    | zero => exact coeff_nil 0
    | succ n => exact (coeff_nil (n + 1)).trans (coeff_nil n).symm
  | cons c cs ih =>
    obtain ⟨qs, h⟩ := ih
    refine ⟨evalPoly cs a :: qs, fun n => ?_⟩
    cases n with
    | zero =>
      show c = (c + a * evalPoly cs a) + (-a) * evalPoly cs a
      rw [CRing.add_assoc, ← CRing.right_distrib, CRing.add_neg, CRing.zero_mul,
        CRing.add_zero]
    | succ n => exact h n

/-- Cor. to Art. 514 (Hall & Knight, *Higher Algebra*), over any commutative ring of
coefficients. The rational integral function `f(x)` is exactly divisible by `x − a`, that is
`f = (x − a)·Q` as polynomials (equal coefficients in every degree) for some rational integral
`Q`, if and only if `f(a) = 0`. So if `f` is exactly divisible by `x − a`, then `f(a) = 0`; and
if `f` vanishes when `x = a`, then it is divisible by `x − a`. -/
theorem hk_art_514_cor (f : List α) (a : α) :
    (∃ qs : List α, ∀ n, coeff f n = coeff (mulLin a qs) n) ↔
      evalPoly f a = CRing.zero := by
  constructor
  · intro ⟨qs, h⟩
    rw [eval_congr f (mulLin a qs) a h, eval_mulLin, CRing.add_neg, CRing.zero_mul]
  · intro hf
    obtain ⟨qs, h⟩ := hk_art_514_div f a
    refine ⟨qs, fun n => ?_⟩
    rw [h n, hf, coeff_addConst_zero]

end Poly

/-- The corollary for integer coefficients, stated with Int's own `0`. -/
theorem hk_art_514_cor_int (f : List Int) (a : Int) :
    (∃ qs : List Int, ∀ n, coeff f n = coeff (mulLin a qs) n) ↔ evalPoly f a = 0 :=
  hk_art_514_cor f a

## lean
Lean accepts the code.

## challenger
NO OBJECTION

## critic
**Recommendation: do not merge.** The final code compiles and fixes the pointwise-identity problem. It still falls short of the issue's prose, and two requests from the challenger and the supervisor were never fully met.

1. **The first objection is still unanswered in checked code.**
   - The challenger's first objection was that "rational integral function" allows rational and real coefficients. The concrete test case was `f(x) = 2x − 1` vanishing at `a = 1/2`, and the challenger named `Rat` as a fix.
   - The prover's reply moved to an abstract `CRing` class. The only instance it supplies is `CRing Int`, which is exactly the special case the objection rejected.
   - The prover now says outright "No `Rat` instance is claimed." The supervisor's alternative was "Int/Rat with real instances." The prover took only the Int half.
   - So nothing in the file shows that the class captures the book's coefficient domains. The test case `2x − 1` at `1/2` is still never stated or checked.
   - The generic theorem is true. But the only rational-coefficient content offered is a reader's assumption that some lawful instance would exist. The file never shows it.

2. **"Exactly divisible" rests on a bespoke definition, not on polynomial multiplication.**
   - The supervisor asked the prover to "define polynomial multiplication and state the conclusion as f = (x − a)·Q."
   - What was delivered is `mulLin a qs`, a special-purpose recursion for multiplying by a linear factor. The only lemma connecting it to a product is `eval_mulLin`, and that lemma is pointwise.
   - That pointwise notion is exactly the one the previous round rejected as too weak over ℤ/p.
   - No general `mulPoly` exists. No lemma shows that `mulLin a qs` has the coefficients of `[-a, 1] * qs` under ordinary multiplication.
   - The coefficient-level meaning of the main theorem therefore depends on reading `mulLin`'s definition by hand. The machine never checks it against the notion the book and supervisor describe.

3. **The statement and its documentation still drift from the prose.**
   - The docstrings call the objects "rational integral functions." They are proved over arbitrary commutative rings, including the trivial ring, since the class has no `zero ≠ one`. In the final file the field `one` is never even used.
   - The issue's framing is the book's: f has rational or real coefficients of n dimensions, and Q is the quotient obtained by dividing. The PR proves a different, more abstract theorem, and only one concrete instance of it is checked.
   - The challenger's late "NO OBJECTION" does not repair this. The gaps in points 1 and 2 are the parts of the earlier objections and the supervisor's instructions that remain unmet.
   - The fix is small: add `Rat` (or a ℤ/p) instance with the example `2x − 1` at `1/2`, and define `mulPoly` with `mulLin a qs` proved equal to `mulPoly [-a, 1] qs` coefficientwise. Until then the PR should not merge.

## defender
**Defender: the PR should merge.** The final theorem states the factor theorem as a true coefficient-level identity, and Lean checks it with no `sorry`.

1. **No `Rat` instance.** The supervisor offered two options: a generic coefficient identity *or* restriction to Int/Rat with real instances. The prover took the first and also checked the Int case, so a `Rat` instance was never required. The theorem holds for every lawful `CRing`, and the class's axioms are the standard commutative-ring axioms that ℚ and ℝ plainly satisfy, so `2x − 1` at `1/2` is covered without anything left to prove.

2. **`mulLin` instead of a general `mulPoly`.** `mulLin` is polynomial multiplication by `x − a`. Its two-line recursion gives coefficient n as `−a·qₙ + qₙ₋₁`, which is exactly the coefficient of `(x − a)·Q`. The conclusion is coefficientwise as the supervisor asked, so the pointwise `eval_mulLin` is used only inside the proof of the easy direction and does not weaken the statement.

3. **Drift from the prose.** Admitting more rings, including the trivial one, only makes a true theorem stronger, and an unused `one` field is harmless. The book's own framing is preserved: `hk_art_514_div` builds Q by dividing (synthetic division) and states R = f(a), and the degree n is just the length of the coefficient list.

## supervisor
**MERGE.** Lean accepts the final code, which states the factor theorem as an equality of coefficients, f = (x − a)·Q ⇔ f(a) = 0, over any commutative ring. This fixes the earlier pointwise weakness, and the `CRing Int` instance shows the class can be satisfied. `mulLin` matches multiplication by x − a coefficient by coefficient (coefficient n+1 is qₙ − a·qₙ₊₁), so a general `mulPoly` is not needed to read the statement correctly. The missing `Rat` instance and the admission of the trivial ring only make a true statement more general, and neither changes its meaning for the book's rational or real coefficients.
