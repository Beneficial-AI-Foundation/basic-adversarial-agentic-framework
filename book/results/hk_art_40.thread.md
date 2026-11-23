## issue
Issue #40. To find the sum of a number of terms in Arithmetical Progression (Art. 40)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter IV (Arithmetical Progression), Art. 40.
The book prints the following text.
38. DEFINITION. Quantities are said to be in Arithmetical Progression when they increase or decrease by a common difference.
39. [...] If n be the number of terms, and if l denote the last, or nth term, we have l = a + (n − 1) d.
Let a denote the first term, d the common difference, and n the number of terms. Also let l denote the last term, and s the required sum; then s = a + (a + d) + (a + 2d) + ... + (l − 2d) + (l − d) + l;
s = (n/2)(a + l) ......(1); and l = a + (n − 1) d ......(2), ∴ s = (n/2){2a + (n − 1) d} ......(3).
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_40.

## prover
/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms
(`a` first term, `d` common difference), as an integer. -/
def apSum (a d : Int) (n : Nat) : Int :=
  ((List.range n).map (fun i : Nat => a + (i : Int) * d)).sum

theorem two_apSum (a d : Int) : ∀ n : Nat,
    2 * apSum a d n = (n : Int) * (2 * a + ((n : Int) - 1) * d)
  | 0 => by simp [apSum]
  | n + 1 => by
    have ih := two_apSum a d n
    have hs : apSum a d (n + 1) = apSum a d n + (a + (n : Int) * d) := by
      simp [apSum, List.range_succ, List.map_append, List.sum_append]
    rw [hs]
    have hc : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by omega
    rw [hc, Int.add_sub_cancel]
    simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.one_mul] at ih ⊢
    omega

/-- Hall & Knight, Higher Algebra, Art. 40.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
To stay in the integers without division, both formulas are stated in the
equivalent doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`. -/
theorem hk_art_40 (a d l : Int) (n : Nat) (hl : l = a + ((n : Int) - 1) * d) :
    2 * apSum a d n = (n : Int) * (a + l) ∧
    2 * apSum a d n = (n : Int) * (2 * a + ((n : Int) - 1) * d) := by
  subst hl
  refine ⟨?_, two_apSum a d n⟩
  rw [two_apSum, Int.two_mul, Int.add_assoc]

## lean
Lean accepts the code.

## challenger
OBJECTION: The theorem fixes the first term `a` and the common difference `d` to be integers. Hall and Knight's Art. 40 covers arbitrary quantities, and the book's own progressions routinely have fractional terms and differences, for example a = 3/4, d = −1/2. So `hk_art_40` proves only a special case of the stated result and does not establish formulas (1) and (3) for the progressions the article is about. The statement should be over a field such as `Rat`, or over an arbitrary commutative ring in the doubled form, so that it is not weaker than the prose.

## prover
-- The objection holds: an integer-only statement is a special case of Art. 40.
-- The result is now stated for any commutative ring `α` (core's `Lean.Grind.CommRing`).
-- This covers `Int`, and also `Rat` with progressions such as a = 3/4, d = -1/2.
-- In a general ring `n/2` is not available, so formulas (1) and (3) appear in the
-- equivalent doubled form `2 s = n (a + l)`.

universe u

/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms:
`apSum a d n = a + (a + d) + … + (a + (n - 1) d)`. -/
def apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : Nat → α
  | 0 => 0
  | n + 1 => apSum a d n + (a + (n : α) * d)

theorem two_apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : ∀ n : Nat,
    2 * apSum a d n = (n : α) * (2 * a + ((n : α) - 1) * d)
  | 0 => by simp only [apSum]; grind
  | n + 1 => by
    have ih := two_apSum a d n
    simp only [apSum]
    grind

/-- Hall & Knight, Higher Algebra, Art. 40, over an arbitrary commutative ring.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
These are stated in the doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`. -/
theorem hk_art_40 {α : Type u} [Lean.Grind.CommRing α] (a d l : α) (n : Nat)
    (hl : l = a + ((n : α) - 1) * d) :
    2 * apSum a d n = (n : α) * (a + l) ∧
    2 * apSum a d n = (n : α) * (2 * a + ((n : α) - 1) * d) := by
  subst hl
  have h := two_apSum a d n
  exact ⟨by grind, h⟩

## lean
The Lean check failed. Lean rejects the code. <stdin>:13:32: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:16:22: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:16:42: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:17:23: warning: declaration uses `sorry`
<stdin>:17:23: warning: declaration uses `sorry`
<stdin>:30:19: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:31:22: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:32:22: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
<stdin>:32:42: error: Type mismatch
  n
has type
  Nat
of sort `Type` but is expected to have type
  α
of sort `Type u`
'hk_art_40' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]


## challenger
OBJECTION: The Lean check failed. Every cast `(n : α)` is rejected with a type mismatch, because `Lean.Grind.CommRing` provides no coercion from `Nat` to `α` in that position. As a result, `two_apSum` and `hk_art_40` depend on `sorryAx`, so nothing about Art. 40 has been proved. A fix must elaborate, for example by writing the cast explicitly as `(OfNat.ofNat n : α)` or `NatCast.natCast n` with an available instance, and it must keep the general-ring statement so that the earlier objection stays answered.

## prover
-- The previous attempt failed because `(n : α)` did not elaborate: no `Nat`-to-`α`
-- coercion was found for a `Lean.Grind.CommRing α`. The fix avoids the coercion:
-- `natElt n` builds the element `1 + 1 + … + 1` (n times) of `α` by recursion, so it
-- is the number `n` inside the ring. The statement keeps the general commutative ring,
-- which covers `Int` and `Rat`, so the earlier objection about integer-only terms
-- stays answered. Formulas (1) and (3) appear in the doubled form, since `n/2` is
-- not available in a general ring.

universe u

/-- The natural number `n` as an element of the ring `α`: `0 + 1 + … + 1` (n ones). -/
def natElt {α : Type u} [Lean.Grind.CommRing α] : Nat → α
  | 0 => 0
  | n + 1 => natElt n + 1

/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms:
`apSum a d n = a + (a + d) + … + (a + (n - 1) d)`. -/
def apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : Nat → α
  | 0 => 0
  | n + 1 => apSum a d n + (a + natElt n * d)

theorem two_apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : ∀ n : Nat,
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d)
  | 0 => by simp only [apSum, natElt]; grind
  | n + 1 => by
    have ih := two_apSum a d n
    simp only [apSum, natElt]
    grind

/-- Hall & Knight, Higher Algebra, Art. 40, over an arbitrary commutative ring.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Here `natElt n` is `n` as an element of the ring.
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
These are stated in the doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`. -/
theorem hk_art_40 {α : Type u} [Lean.Grind.CommRing α] (a d l : α) (n : Nat)
    (hl : l = a + (natElt n - 1) * d) :
    2 * apSum a d n = natElt n * (a + l) ∧
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d) := by
  subst hl
  have h := two_apSum a d n
  exact ⟨by grind, h⟩

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The code now elaborates, and `hk_art_40` depends on no `sorryAx`, so the failed check from the previous turn is fixed. The general-ring statement still answers the earlier objection that the result held only for integers, since it covers `Int` and `Rat`.

- **`natElt` is faithful.** It is defined as `0 + 1 + … + 1` with `n` ones, which is exactly the integer `n` inside the ring.
- **`apSum` is faithful.** It sums `a + k·d` for `k = 0, …, n − 1`, which is the book's `a + (a + d) + … + l`.
- **`hl` is faithful.** It encodes equation (2), `l = a + (n − 1)d`.
- **The doubled form is not weaker.** It says `2s = n(a + l)` and `2s = n{2a + (n − 1)d}`. For the quantities the article treats, such as rationals, this is equivalent to formulas (1) and (3), because 2 is invertible there.

## critic
1. **The theorem never states the book's formulas (1) and (3).** Art. 40 gives `s = (n/2)(a + l)` and `s = (n/2){2a + (n − 1)d}`. `hk_art_40` proves only `2s = n(a + l)` and `2s = n{2a + (n − 1)d}`, over an arbitrary `Lean.Grind.CommRing`. That class includes rings of characteristic 2. In such a ring the left side `2s` is 0. The right side is `n(n − 1)d` once `2a` is dropped, and `n(n − 1)` is always even, so it is 0 as well. The theorem is then `0 = 0` and says nothing about `s`. The doubled form matches the book only where 2 is invertible. That fact appears in a docstring and in the challenger's sign-off, not in any Lean statement. The fix is cheap and was never done:
   - state `s = (n/2)(a + l)` over a field such as `Rat`, or
   - add a hypothesis that 2 is invertible and derive (1) and (3) in their printed form.

2. **The claim that the theorem "covers `Rat`" is asserted, not checked.** The final statement is not written in terms of the number `n` as the ring usually sees it, `(n : α)`. It uses an ad hoc recursive `natElt`. No lemma connects `natElt n` to the ring's own natural-number cast or literals. No instance or example applies `hk_art_40` to `Rat`, or to the challenger's progression `a = 3/4, d = −1/2`. Using the theorem for the book's fractional progressions would need an unproved bridge lemma. It would also need a `Lean.Grind.CommRing Rat` instance, whose existence in core is never demonstrated in the file.

3. **The prover did not truly answer the challenger's first objection.** That objection asked for a statement "not weaker than the prose" and named a field such as `Rat` as the natural home. The prover chose the general-ring route instead. This brings back the weakness in point 1, because the general statement is weaker than the book exactly where 2 is not invertible. It then covers the gap with prose comments rather than proof. The challenger's final "NO OBJECTION" rests on the sentence "because 2 is invertible there", which is a premise absent from the theorem. Lean accepting the code shows only that this doubled, coercion-free variant is true. It does not show that Art. 40 as printed has been formalized. The PR should not merge until (1) and (3) appear in their stated form, at least for `Rat`.

## defender
1. **Rebut.** The printed `(n/2)` only has meaning where 2 is invertible, and in every such ring the doubled identity gives (1) and (3) by multiplying both sides by `2⁻¹`. In characteristic 2 the book's formula cannot be stated at all, so the theorem saying little there removes nothing from Art. 40, and the general-ring version is at least as strong as a `Rat`-only doubled statement.

2. **Concede.** Nothing in the file shows that the theorem applies to `Rat` or to `a = 3/4, d = −1/2`. There is no lemma linking `natElt n` to `(n : α)`, and no demonstrated `Lean.Grind.CommRing Rat` instance or example. The definition of `natElt` is transparently `n` ones, so a bridge lemma would be a short induction, but "covers `Rat`" is asserted rather than checked and should be backed by such a lemma and an example.

3. **Rebut.** The generalization strengthens the theorem: any instance, including any field, is a specialization, so no case the book treats has been lost. "2 is invertible" is not a hidden premise the theorem relies on; it is the condition under which the book's `n/2` even makes sense. The doubled form is a standard division-free encoding of "state the result", and the summation identity it proves is the whole mathematical content of Art. 40.

## supervisor
REVISE. Lean accepts the code, and the doubled form is a fair encoding wherever `n/2` makes sense. However, the critic's second point stands, and the defender conceded it: nothing in the file ties the ad hoc `natElt n` to the ring's own natural-number cast, and nothing shows the theorem applies to `Rat` or to the progression `a = 3/4, d = −1/2`. Add a bridge lemma `natElt n = (NatCast.natCast n : α)` (a short induction), and add a corollary over `Rat` that states (1) and (3) in their printed form `s = (n/2)(a + l)` and `s = (n/2){2a + (n − 1)d}`, checked on that example.

## prover
-- Revision for the supervisor's REVISE, following the critic's second point, which the defender conceded.
-- 1. `natElt_eq_natCast` is the bridge lemma. It proves `natElt n = (NatCast.natCast n : α)`
--    by induction, using the ring's own `Nat` cast from `Lean.Grind.Semiring`.
-- 2. `hk_art_40_rat` is the corollary over `Rat`. It states (1) and (3) in their printed form
--    `s = (n/2)(a + l)` and `s = (n/2){2a + (n - 1)d}`.
-- 3. The challenger's progression `a = 3/4, d = -1/2` is checked with 4 terms, so `l = -3/4`.
--    Formulas (1) and (3) both give `s = 0` there.
-- Not yet run through the checker. The cast lemma names and the `Rat` ring instance are assumed from core.

universe u

/-- The natural number `n` as an element of the ring `α`: `0 + 1 + … + 1` (n ones). -/
def natElt {α : Type u} [Lean.Grind.CommRing α] : Nat → α
  | 0 => 0
  | n + 1 => natElt n + 1

/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms:
`apSum a d n = a + (a + d) + … + (a + (n - 1) d)`. -/
def apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : Nat → α
  | 0 => 0
  | n + 1 => apSum a d n + (a + natElt n * d)

attribute [local instance] Lean.Grind.Semiring.natCast

/-- Bridge lemma: `natElt n` is the ring's own cast of the natural number `n`. -/
theorem natElt_eq_natCast {α : Type u} [Lean.Grind.CommRing α] (n : Nat) :
    natElt n = (NatCast.natCast n : α) := by
  induction n with
  | zero =>
    simp only [natElt]
    exact (Lean.Grind.Semiring.natCast_zero).symm
  | succ n ih =>
    simp only [natElt]
    rw [ih]
    exact (Lean.Grind.Semiring.natCast_succ n).symm

theorem two_apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : ∀ n : Nat,
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d)
  | 0 => by simp only [apSum, natElt]; grind
  | n + 1 => by
    have ih := two_apSum a d n
    simp only [apSum, natElt]
    grind

/-- Hall & Knight, Higher Algebra, Art. 40, over an arbitrary commutative ring.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Here `natElt n` is `n` as an element of the ring (see `natElt_eq_natCast`).
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
These are stated in the doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`.
The printed form over `Rat` is `hk_art_40_rat`. -/
theorem hk_art_40 {α : Type u} [Lean.Grind.CommRing α] (a d l : α) (n : Nat)
    (hl : l = a + (natElt n - 1) * d) :
    2 * apSum a d n = natElt n * (a + l) ∧
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d) := by
  subst hl
  have h := two_apSum a d n
  exact ⟨by grind, h⟩

/-- `natElt n` is the usual rational number `n`. -/
theorem natElt_rat (n : Nat) : (natElt n : Rat) = (n : Rat) := by
  induction n with
  | zero => simp only [natElt]; grind
  | succ n ih =>
    simp only [natElt]
    rw [ih]
    first
      | grind
      | simp
      | exact (natElt_eq_natCast (α := Rat) (n + 1))

/-- Hall & Knight, Art. 40, over `Rat`, in the printed form:
with `l = a + (n - 1) d` (2), the sum `s` of the `n` terms satisfies
`s = (n/2)(a + l)` (1) and `s = (n/2){2a + (n - 1) d}` (3). -/
theorem hk_art_40_rat (a d l : Rat) (n : Nat) (hl : l = a + ((n : Rat) - 1) * d) :
    apSum a d n = ((n : Rat) / 2) * (a + l) ∧
    apSum a d n = ((n : Rat) / 2) * (2 * a + ((n : Rat) - 1) * d) := by
  have hb := natElt_rat n
  have h := hk_art_40 a d l n (by rw [hb]; exact hl)
  rw [hb] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · grind
  · grind

/-- The book-style progression `3/4, 1/4, -1/4, -3/4` (a = 3/4, d = -1/2, n = 4, l = -3/4):
formula (1) applies and gives the sum 0. -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).1
  rw [h]
  grind

/-- The same progression through formula (3). -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).2
  rw [h]
  grind

## lean
Lean accepts the code.

## challenger
NO OBJECTION

Lean accepts the code. The supervisor's requested revision is in place:
- `natElt_eq_natCast` ties `natElt n` to the ring's own natural-number cast.
- `natElt_rat` ties `natElt n` to the standard `(n : Rat)` coercion.
- `hk_art_40_rat` states formulas (1) and (3) in the book's printed form `s = (n/2)(a + l)` and `s = (n/2){2a + (n − 1)d}` over `Rat`, with hypothesis (2).

The two examples confirm my progression `3/4, 1/4, −1/4, −3/4` and its correct sum 0 through both formulas. The `n = 0` case is harmless, since both sides are 0. I can defend no further objection.

## critic
1. **The theorem named `hk_art_40` still does not state the result of Art. 40.**
   - The issue says the main theorem must be `hk_art_40`, and it must state the article's result: `s = (n/2)(a + l)` (1) and `s = (n/2){2a + (n − 1)d}` (3).
   - The final `hk_art_40` is unchanged. It is the doubled, division-free identity over an arbitrary `Lean.Grind.CommRing`. In characteristic 2 it reduces to `0 = 0` and says nothing about `s`.
   - The printed formulas appear only in a secondary corollary, `hk_art_40_rat`.
   - The revision added the book's statement next to the main theorem instead of making it the main theorem. A reader who checks `hk_art_40`, as the issue directs, still finds a statement that matches the book only under the premise "2 is invertible". That premise is not in its type.
   - The fix is cheap: rename so the printed `Rat` form is `hk_art_40` and the doubled ring form is a helper lemma. It was not done.

2. **The worked example does not test the formula it claims to confirm.**
   - The progression `3/4, 1/4, −1/4, −3/4` has `a + l = 0` and sum 0.
   - So `(n/2)(a + l) = 0` holds whatever the factor in front is. `n·(a + l)`, `(n/4)(a + l)` or `0·(a + l)` would all "confirm" it equally.
   - Formula (3) is likewise satisfied for any coefficient, because `2a + (n − 1)d = 0`.
   - The challenger's sign-off rests on two examples that cannot tell the book's `n/2` from a wrong factor. They are not evidence that the `Rat` corollary was sanity-checked on a genuine fractional progression.
   - A check with nonzero sum is needed, for example `a = 3/4, d = −1/2, n = 3`, with sum `3/4`.

3. **The revised file is unreviewed, guess-driven code with a stale, false comment.**
   - The header still says "Not yet run through the checker. The cast lemma names and the `Rat` ring instance are assumed from core." That comment would be merged as-is.
   - `natElt_rat` closes its step with `first | grind | simp | exact (natElt_eq_natCast …)`. This is a shotgun combinator: the author did not know which tactic works, and the third branch does not even target the stated goal.
   - The bridge lemma `natElt_eq_natCast` was the supervisor's explicit requirement, yet it is never used by `hk_art_40_rat`. It is proved under `attribute [local instance] Lean.Grind.Semiring.natCast`, a file-wide instance override, so it ties `natElt` to that local instance rather than demonstrably to the cast users write.
   - Lean accepting this shows only that some branch happened to fire. A PR whose own header says it was not checked, and that leaves dead and fragile proof code, should not merge until it is cleaned up and the main theorem is the printed statement.

## defender
1. **Rebut.** The supervisor already ruled the doubled form a fair encoding of Art. 40 and asked only for an added `Rat` corollary in printed form, which `hk_art_40_rat` supplies and derives directly from `hk_art_40`. The general-ring `hk_art_40` gives the printed formulas in every ring where `n/2` exists, and in characteristic 2 the book's statement cannot even be written, so being trivial there loses nothing from the article.

2. **Rebut.** The factor `n/2` is established by the proof of `hk_art_40_rat` for every `n` and every rational `a`, `d`, not by the example, so a wrong factor is already excluded. The example's job, as the supervisor set it, was to show that the corollary actually applies to `Rat` and to the progression `a = 3/4, d = −1/2`, and Lean confirms that it does.

3. **Concede in part.** The header comment saying the code was not yet checked is stale, and the third `first` branch is dead code; both should be removed before merge. Neither affects soundness: Lean checked every proof, `Lean.Grind.Semiring.natCast` is the ring structure's own `Nat` cast rather than an override, and `natElt_rat`, which `hk_art_40_rat` uses, ties `natElt` to the standard `(n : Rat)` coercion.

## supervisor
REVISE. Lean accepts the code, and the doubled general-ring `hk_art_40` together with the printed-form `hk_art_40_rat` matches Art. 40. However, the critic's third point stands in part, as the defender conceded: the file still carries a false header saying it was not run through the checker, and `natElt_rat` uses a guess-driven `first | grind | simp | exact …` with a branch that does not even target its goal. Remove the stale comment, replace the `first` combinator with the single tactic that closes the step, and either use `natElt_eq_natCast` or drop it with its `local instance` attribute. Also add a nonzero-sum check such as `apSum (3/4 : Rat) (-1/2) 3 = 3/4` through both formulas, so the examples can tell the factor `n/2` from a wrong one.

## prover
-- Revision for the supervisor's second REVISE:
-- 1. Removed the stale header that said the code had not been run through the checker.
-- 2. In `natElt_rat`, replaced the `first | grind | simp | exact …` combinator with a single
--    `grind`, the same tactic that closes the zero case of that lemma.
-- 3. Dropped the unused bridge lemma `natElt_eq_natCast` and its `local instance` attribute.
--    `natElt_rat` remains the bridge that `hk_art_40_rat` uses.
-- 4. Added a check with nonzero sum: a = 3/4, d = -1/2, n = 3, l = -1/4.
--    The terms are 3/4, 1/4, -1/4, so the sum is 3/4, and both formulas give 3/4.
--    Unlike the n = 4 progression, here a + l ≠ 0, so this check tests the factor n/2.

universe u

/-- The natural number `n` as an element of the ring `α`: `0 + 1 + … + 1` (n ones). -/
def natElt {α : Type u} [Lean.Grind.CommRing α] : Nat → α
  | 0 => 0
  | n + 1 => natElt n + 1

/-- Sum of the arithmetical progression `a, a + d, a + 2d, …` taken to `n` terms:
`apSum a d n = a + (a + d) + … + (a + (n - 1) d)`. -/
def apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : Nat → α
  | 0 => 0
  | n + 1 => apSum a d n + (a + natElt n * d)

theorem two_apSum {α : Type u} [Lean.Grind.CommRing α] (a d : α) : ∀ n : Nat,
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d)
  | 0 => by simp only [apSum, natElt]; grind
  | n + 1 => by
    have ih := two_apSum a d n
    simp only [apSum, natElt]
    grind

/-- Hall & Knight, Higher Algebra, Art. 40, over an arbitrary commutative ring.
Let `a` be the first term, `d` the common difference and `n` the number of terms
of an arithmetical progression, and let `l = a + (n - 1) d` be the last term (2).
Here `natElt n` is `n` as an element of the ring (over `Rat`, see `natElt_rat`).
Then the sum `s = a + (a + d) + … + l` satisfies `s = (n/2)(a + l)` (1) and
`s = (n/2){2a + (n - 1) d}` (3).
These are stated in the doubled form `2 s = n (a + l)` and `2 s = n {2a + (n - 1) d}`.
The printed form over `Rat` is `hk_art_40_rat`. -/
theorem hk_art_40 {α : Type u} [Lean.Grind.CommRing α] (a d l : α) (n : Nat)
    (hl : l = a + (natElt n - 1) * d) :
    2 * apSum a d n = natElt n * (a + l) ∧
    2 * apSum a d n = natElt n * (2 * a + (natElt n - 1) * d) := by
  subst hl
  have h := two_apSum a d n
  exact ⟨by grind, h⟩

/-- `natElt n` is the usual rational number `n`. -/
theorem natElt_rat (n : Nat) : (natElt n : Rat) = (n : Rat) := by
  induction n with
  | zero => simp only [natElt]; grind
  | succ n ih =>
    simp only [natElt]
    rw [ih]
    grind

/-- Hall & Knight, Art. 40, over `Rat`, in the printed form:
with `l = a + (n - 1) d` (2), the sum `s` of the `n` terms satisfies
`s = (n/2)(a + l)` (1) and `s = (n/2){2a + (n - 1) d}` (3). -/
theorem hk_art_40_rat (a d l : Rat) (n : Nat) (hl : l = a + ((n : Rat) - 1) * d) :
    apSum a d n = ((n : Rat) / 2) * (a + l) ∧
    apSum a d n = ((n : Rat) / 2) * (2 * a + ((n : Rat) - 1) * d) := by
  have hb := natElt_rat n
  have h := hk_art_40 a d l n (by rw [hb]; exact hl)
  rw [hb] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · grind
  · grind

/-- The book-style progression `3/4, 1/4, -1/4, -3/4` (a = 3/4, d = -1/2, n = 4, l = -3/4):
formula (1) applies and gives the sum 0. -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).1
  rw [h]
  grind

/-- The same progression through formula (3). -/
example : apSum (3/4 : Rat) (-1/2) 4 = 0 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-3/4) 4 (by grind)).2
  rw [h]
  grind

/-- A nonzero-sum check: `3/4, 1/4, -1/4` (a = 3/4, d = -1/2, n = 3, l = -1/4).
Formula (1) gives `(3/2)(3/4 - 1/4) = 3/4`. -/
example : apSum (3/4 : Rat) (-1/2) 3 = 3/4 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-1/4) 3 (by grind)).1
  rw [h]
  grind

/-- The same progression through formula (3): `(3/2)(3/2 + 2·(-1/2)) = 3/4`. -/
example : apSum (3/4 : Rat) (-1/2) 3 = 3/4 := by
  have h := (hk_art_40_rat (3/4) (-1/2) (-1/4) 3 (by grind)).2
  rw [h]
  grind

## lean
Lean accepts the code.

## challenger
NO OBJECTION

Lean accepts the code, and every point of the supervisor's second REVISE is addressed:
- **Stale header removed.** The comment saying the code had not been run through the checker is gone.
- **Guessing combinator replaced.** `natElt_rat` now closes its step with a single `grind` instead of `first | grind | simp | exact …`.
- **Unused bridge dropped.** `natElt_eq_natCast` and its `local instance` attribute are removed. `natElt_rat` remains the bridge that `hk_art_40_rat` actually uses.
- **Nonzero-sum check added.** The progression `3/4, 1/4, −1/4` has sum 3/4 by hand. Formula (1) gives `(3/2)·(1/2) = 3/4` and formula (3) gives `(3/2)·(3/2 − 1) = 3/4`, both checked by Lean. Here `a + l ≠ 0`, so the check can tell the factor `n/2` from a wrong one.

The remaining critic point, that `hk_art_40` is in doubled general-ring form, was ruled a fair encoding by the supervisor. The printed form `s = (n/2)(a + l)` and `s = (n/2){2a + (n − 1)d}` is proved over `Rat` from that theorem with hypothesis (2). I can defend no further objection.

## critic
1. **The theorem the issue names still does not state Art. 40.**
   - The issue says the main theorem must be `hk_art_40` and must state the article's result: `s = (n/2)(a + l)` and `s = (n/2){2a + (n − 1)d}`.
   - The final `hk_art_40` is unchanged across both revisions. It proves only the doubled identity `2s = n(a + l)` over an arbitrary `Lean.Grind.CommRing`.
   - In characteristic 2 it collapses to `0 = 0`. Where 2 is invertible it matches the book only under a premise that its type never states.
   - The printed formulas exist only in a side corollary, `hk_art_40_rat`, and only over `Rat`.
   - Hall and Knight's quantities include surds as well as rationals. For any field other than `Rat`, no theorem gives `s = (n/2)(a + l)`. Users get only the doubled form and must divide by 2 themselves.
   - Two ways to fix it were never taken:
     - rename so the printed form is `hk_art_40` and the ring identity is a helper, or
     - state the printed form under a hypothesis that 2 is invertible.

2. **The supervisor's own bridge requirement was quietly reversed.**
   - The first REVISE asked for `natElt n = (NatCast.natCast n : α)` because nothing tied the ad hoc `natElt` to the ring's actual number `n`.
   - The final file deletes that lemma.
   - So for every ring except `Rat`, the general theorem is again stated in terms of a private recursion with no proved link to `(n : α)`. This includes `Int`, which the prover repeatedly claimed is "covered."
   - The docstring of `hk_art_40` still asserts "`natElt n` is `n` as an element of the ring." Only `natElt_rat` backs that, and only for `Rat`.
   - This brings back exactly the gap the defender conceded in point 2 of the first round. The second REVISE permitted dropping the lemma, but that does not make the general-ring claims checked. It only removes the evidence for them.

3. **The prover never actually answered the challenger's first objection.**
   - That objection was that the statement must not be weaker than the prose, ideally stated over a field.
   - The answer was a general-ring theorem that is strictly weaker than the prose wherever 2 is not invertible. A `Rat`-only corollary was then bolted on.
   - The challenger's final sign-off says the remaining concern "was ruled a fair encoding by the supervisor." That defers to a ruling; it is not a demonstration that the objection was met.
   - Lean's acceptance shows that the doubled identity, the `Rat` corollary and four numeric examples are true. It does not show that the theorem the issue designates formalizes Art. 40 as printed.
   - Until `hk_art_40` itself carries formulas (1) and (3), or the general version carries an explicit invertibility hypothesis and a real cast, this PR should not merge.

## defender
1. **Rebut.** The supervisor ruled twice that the doubled general-ring `hk_art_40` is a fair encoding, and `hk_art_40_rat` derives the printed formulas (1) and (3) from it inside the file. In any field, surds included, the printed form follows by multiplying both sides by `2⁻¹`, and in characteristic 2 the book's `n/2` cannot be written at all, so nothing the article states is missing.

2. **Rebut.** The second REVISE explicitly allowed the prover to "either use `natElt_eq_natCast` or drop it", so dropping it carries out the ruling rather than reversing it. `natElt n` is by its transparent definition the sum `1 + … + 1` of `n` ones, which is what `n` means in any ring, so the docstring is true by definition. The link to the standard coercion is proved where the printed form is claimed, through `natElt_rat`.

3. **Rebut.** The challenger asked for a statement not weaker than the prose, preferably over a field such as `Rat`, and the PR delivers exactly that in `hk_art_40_rat`. That corollary is backed by a general theorem that specializes to every commutative ring, and it is weaker than the prose only in characteristic 2, where the prose itself says nothing. Lean checked every proof, including the nonzero-sum example that pins down the factor `n/2`, and the challenger confirmed the definitions faithful, so the PR should merge.

## supervisor
**MERGE.** Lean accepts the final code, and `hk_art_40` proves the doubled identities `2s = n(a + l)` and `2s = n{2a + (n − 1)d}` under hypothesis (2), with `natElt n` defined as the sum of `n` ones. This matches the book wherever its `n/2` can be written, and `hk_art_40_rat` derives the printed formulas (1) and (3) from it over `Rat`, checked on a nonzero-sum progression that pins down the factor `n/2`. The critic's remaining points restate concerns already settled: the doubled form loses nothing the article states, and dropping the unused cast lemma was explicitly allowed and leaves `natElt` faithful by its definition.
