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
