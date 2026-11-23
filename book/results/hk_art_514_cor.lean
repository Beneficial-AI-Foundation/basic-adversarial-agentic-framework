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
