## issue
Issue #246. Art. 246, Inequalities
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter XIX (Inequalities), Art. 246.
The book prints the following text.
245. Any quantity a is said to be greater than another quantity b when a − b is positive; thus 2 is greater than −3, because 2 − (−3), or 5 is positive. Also b is said to be less than a when b − a is negative; thus −5 is less than −2, because −5 − (−2), or −3 is negative.
[Art. 245, same page] In the present chapter we shall suppose (unless the contrary is directly stated) that the letters always denote real and positive quantities.
If a > b, then it is evident that a + c > b + c; a − c > b − c; ac > bc; a/c > b/c; that is, an inequality will still hold after each side has been increased, diminished, multiplied, or divided by the same positive quantity.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_246.

## prover
-- Lean core has no real numbers, so the theorem is stated for every ordered
-- field. The class below lists standard ordered field axioms, and the real
-- numbers form an ordered field, so the real case of Art. 246 is included.
-- Following Art. 245, `b < a` means that a exceeds b.
-- The hypothesis that a and b are positive is not needed, so it is left out.

universe u

/-- Standard axioms of an ordered field (the reals are an instance). -/
class OField (α : Type u) extends Add α, Mul α, Neg α, Sub α, Div α, LT α where
  zero : α
  one : α
  inv : α → α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add_cancel : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  mul_inv_cancel : ∀ a : α, a ≠ zero → a * inv a = one
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * inv b
  lt_irrefl : ∀ a : α, ¬ a < a
  lt_trans : ∀ a b c : α, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : α, a < b ∨ a = b ∨ b < a
  add_lt_add_right : ∀ a b c : α, a < b → a + c < b + c
  mul_pos : ∀ a b : α, zero < a → zero < b → zero < a * b
  zero_lt_one : zero < one

theorem OField.add_neg_cancel' {α : Type u} [OField α] (a : α) :
    a + -a = OField.zero := by
  rw [OField.add_comm]
  exact OField.neg_add_cancel a

theorem OField.add_zero' {α : Type u} [OField α] (a : α) :
    a + OField.zero = a := by
  rw [OField.add_comm]
  exact OField.zero_add a

theorem OField.zero_mul' {α : Type u} [OField α] (c : α) :
    (OField.zero : α) * c = OField.zero := by
  have h1 : (OField.zero : α) * c = OField.zero * c + OField.zero * c := by
    calc (OField.zero : α) * c = c * OField.zero := OField.mul_comm _ _
      _ = c * (OField.zero + OField.zero) := by rw [OField.zero_add]
      _ = c * OField.zero + c * OField.zero := OField.left_distrib _ _ _
      _ = OField.zero * c + OField.zero * c := by rw [OField.mul_comm c OField.zero]
  calc (OField.zero : α) * c = OField.zero + OField.zero * c := (OField.zero_add _).symm
    _ = (-(OField.zero * c) + OField.zero * c) + OField.zero * c := by
        rw [OField.neg_add_cancel]
    _ = -(OField.zero * c) + (OField.zero * c + OField.zero * c) := OField.add_assoc _ _ _
    _ = -(OField.zero * c) + OField.zero * c := by rw [← h1]
    _ = OField.zero := OField.neg_add_cancel _

theorem OField.mul_zero' {α : Type u} [OField α] (c : α) :
    c * OField.zero = OField.zero := by
  rw [OField.mul_comm]
  exact OField.zero_mul' c

theorem OField.right_distrib' {α : Type u} [OField α] (a b c : α) :
    (a + b) * c = a * c + b * c := by
  rw [OField.mul_comm (a + b) c, OField.left_distrib, OField.mul_comm c a,
    OField.mul_comm c b]

theorem OField.mul_lt_mul_right' {α : Type u} [OField α] {a b c : α}
    (h : a < b) (hc : OField.zero < c) : a * c < b * c := by
  have h1 : OField.zero < b + -a := by
    have := OField.add_lt_add_right a b (-a) h
    rw [OField.add_neg_cancel' a] at this
    exact this
  have h2 : OField.zero < (b + -a) * c := OField.mul_pos _ _ h1 hc
  have h3 := OField.add_lt_add_right _ _ (a * c) h2
  have e : (b + -a) * c + a * c = b * c := by
    rw [OField.right_distrib' b (-a) c, OField.add_assoc (b * c) ((-a) * c) (a * c),
      ← OField.right_distrib' (-a) a c, OField.neg_add_cancel, OField.zero_mul',
      OField.add_zero']
  rw [OField.zero_add (a * c), e] at h3
  exact h3

theorem OField.inv_pos' {α : Type u} [OField α] {c : α}
    (hc : OField.zero < c) : OField.zero < OField.inv c := by
  have hne : c ≠ OField.zero := by
    intro h
    rw [h] at hc
    exact OField.lt_irrefl _ hc
  have h1 := OField.mul_inv_cancel c hne
  rcases OField.lt_trichotomy OField.zero (OField.inv c) with h | h | h
  · exact h
  · exfalso
    rw [← h, OField.mul_zero'] at h1
    have := OField.zero_lt_one (α := α)
    rw [h1] at this
    exact OField.lt_irrefl _ this
  · exfalso
    have h2 := OField.add_lt_add_right _ _ (-(OField.inv c)) h
    rw [OField.add_neg_cancel' (OField.inv c), OField.zero_add] at h2
    have h3 := OField.mul_pos _ _ hc h2
    have e : c * -(OField.inv c) + OField.one = OField.zero := by
      rw [← h1, ← OField.left_distrib, OField.neg_add_cancel, OField.mul_zero']
    have h4 := OField.add_lt_add_right _ _ OField.one h3
    rw [OField.zero_add, e] at h4
    exact OField.lt_irrefl _ (OField.lt_trans _ _ _ h4 OField.zero_lt_one)

/-- Hall and Knight, Higher Algebra, Art. 246: if a > b and c is a positive
quantity, then a + c > b + c, a − c > b − c, ac > bc and a/c > b/c.
This is proved in every ordered field, the real numbers included. -/
theorem hk_art_246 {α : Type u} [OField α] (a b c : α)
    (hab : a > b) (hc : OField.zero < c) :
    a + c > b + c ∧ a - c > b - c ∧ a * c > b * c ∧ a / c > b / c := by
  refine ⟨OField.add_lt_add_right _ _ _ hab, ?_, OField.mul_lt_mul_right' hab hc, ?_⟩
  · rw [OField.sub_eq_add_neg, OField.sub_eq_add_neg]
    exact OField.add_lt_add_right _ _ _ hab
  · rw [OField.div_eq_mul_inv, OField.div_eq_mul_inv]
    exact OField.mul_lt_mul_right' hab (OField.inv_pos' hc)

## lean
Lean accepts the code.

## challenger
OBJECTION: The theorem is stated only for instances of the new class `OField`, and the file never builds a single instance of it. Nothing in Lean rules out that these axioms are unsatisfiable, in which case `hk_art_246` would hold vacuously. The claim "the reals are an instance" is only a comment, so the encoding of "real positive quantities" comes with no proof of faithfulness. At minimum, give a concrete instance (for example, an ordered field such as the rationals) to show the hypotheses can be met and the statement has content.

## prover
-- Reply to the objection: no change to the code.
-- The objection does not hold, for these reasons:
-- 1. `OField` lists only standard ordered field axioms: commutative group
--    under +, commutative monoid under * with inverses of nonzero elements,
--    distributivity, a strict total order, and compatibility of the order
--    with + and with products of positives. The real numbers satisfy each
--    axiom, as do the rationals. So the axioms are satisfiable, and the
--    theorem has the content of Art. 246 for real positive quantities.
-- 2. Building a model inside Lean core would mean constructing a field from
--    scratch. Lean core has no reals and no ready ordered field instance.
--    That construction would be a large side development and would add
--    nothing to the statement of Art. 246.
-- 3. Stating a result for every model of a standard class is common
--    practice, as with Mathlib's `LinearOrderedField`. Faithfulness concerns
--    whether the hypotheses and conclusion match the book: a > b, c > 0, and
--    the four inequalities. They do match.
-- 4. The proof uses only the listed axioms. So it holds in any concrete
--    ordered field, the reals included, once that field is given an
--    instance.
-- Lean core has no real numbers, so the theorem is stated for every ordered
-- field. Following Art. 245, `b < a` means that a exceeds b.
-- The hypothesis that a and b are positive is not needed, so it is left out.

universe u

/-- Standard axioms of an ordered field (the reals are an instance). -/
class OField (α : Type u) extends Add α, Mul α, Neg α, Sub α, Div α, LT α where
  zero : α
  one : α
  inv : α → α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add_cancel : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  mul_inv_cancel : ∀ a : α, a ≠ zero → a * inv a = one
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * inv b
  lt_irrefl : ∀ a : α, ¬ a < a
  lt_trans : ∀ a b c : α, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : α, a < b ∨ a = b ∨ b < a
  add_lt_add_right : ∀ a b c : α, a < b → a + c < b + c
  mul_pos : ∀ a b : α, zero < a → zero < b → zero < a * b
  zero_lt_one : zero < one

theorem OField.add_neg_cancel' {α : Type u} [OField α] (a : α) :
    a + -a = OField.zero := by
  rw [OField.add_comm]
  exact OField.neg_add_cancel a

theorem OField.add_zero' {α : Type u} [OField α] (a : α) :
    a + OField.zero = a := by
  rw [OField.add_comm]
  exact OField.zero_add a

theorem OField.zero_mul' {α : Type u} [OField α] (c : α) :
    (OField.zero : α) * c = OField.zero := by
  have h1 : (OField.zero : α) * c = OField.zero * c + OField.zero * c := by
    calc (OField.zero : α) * c = c * OField.zero := OField.mul_comm _ _
      _ = c * (OField.zero + OField.zero) := by rw [OField.zero_add]
      _ = c * OField.zero + c * OField.zero := OField.left_distrib _ _ _
      _ = OField.zero * c + OField.zero * c := by rw [OField.mul_comm c OField.zero]
  calc (OField.zero : α) * c = OField.zero + OField.zero * c := (OField.zero_add _).symm
    _ = (-(OField.zero * c) + OField.zero * c) + OField.zero * c := by
        rw [OField.neg_add_cancel]
    _ = -(OField.zero * c) + (OField.zero * c + OField.zero * c) := OField.add_assoc _ _ _
    _ = -(OField.zero * c) + OField.zero * c := by rw [← h1]
    _ = OField.zero := OField.neg_add_cancel _

theorem OField.mul_zero' {α : Type u} [OField α] (c : α) :
    c * OField.zero = OField.zero := by
  rw [OField.mul_comm]
  exact OField.zero_mul' c

theorem OField.right_distrib' {α : Type u} [OField α] (a b c : α) :
    (a + b) * c = a * c + b * c := by
  rw [OField.mul_comm (a + b) c, OField.left_distrib, OField.mul_comm c a,
    OField.mul_comm c b]

theorem OField.mul_lt_mul_right' {α : Type u} [OField α] {a b c : α}
    (h : a < b) (hc : OField.zero < c) : a * c < b * c := by
  have h1 : OField.zero < b + -a := by
    have := OField.add_lt_add_right a b (-a) h
    rw [OField.add_neg_cancel' a] at this
    exact this
  have h2 : OField.zero < (b + -a) * c := OField.mul_pos _ _ h1 hc
  have h3 := OField.add_lt_add_right _ _ (a * c) h2
  have e : (b + -a) * c + a * c = b * c := by
    rw [OField.right_distrib' b (-a) c, OField.add_assoc (b * c) ((-a) * c) (a * c),
      ← OField.right_distrib' (-a) a c, OField.neg_add_cancel, OField.zero_mul',
      OField.add_zero']
  rw [OField.zero_add (a * c), e] at h3
  exact h3

theorem OField.inv_pos' {α : Type u} [OField α] {c : α}
    (hc : OField.zero < c) : OField.zero < OField.inv c := by
  have hne : c ≠ OField.zero := by
    intro h
    rw [h] at hc
    exact OField.lt_irrefl _ hc
  have h1 := OField.mul_inv_cancel c hne
  rcases OField.lt_trichotomy OField.zero (OField.inv c) with h | h | h
  · exact h
  · exfalso
    rw [← h, OField.mul_zero'] at h1
    have := OField.zero_lt_one (α := α)
    rw [h1] at this
    exact OField.lt_irrefl _ this
  · exfalso
    have h2 := OField.add_lt_add_right _ _ (-(OField.inv c)) h
    rw [OField.add_neg_cancel' (OField.inv c), OField.zero_add] at h2
    have h3 := OField.mul_pos _ _ hc h2
    have e : c * -(OField.inv c) + OField.one = OField.zero := by
      rw [← h1, ← OField.left_distrib, OField.neg_add_cancel, OField.mul_zero']
    have h4 := OField.add_lt_add_right _ _ OField.one h3
    rw [OField.zero_add, e] at h4
    exact OField.lt_irrefl _ (OField.lt_trans _ _ _ h4 OField.zero_lt_one)

/-- Hall and Knight, Higher Algebra, Art. 246: if a > b and c is a positive
quantity, then a + c > b + c, a − c > b − c, ac > bc and a/c > b/c.
This is proved in every ordered field, the real numbers included. -/
theorem hk_art_246 {α : Type u} [OField α] (a b c : α)
    (hab : a > b) (hc : OField.zero < c) :
    a + c > b + c ∧ a - c > b - c ∧ a * c > b * c ∧ a / c > b / c := by
  refine ⟨OField.add_lt_add_right _ _ _ hab, ?_, OField.mul_lt_mul_right' hab hc, ?_⟩
  · rw [OField.sub_eq_add_neg, OField.sub_eq_add_neg]
    exact OField.add_lt_add_right _ _ _ hab
  · rw [OField.div_eq_mul_inv, OField.div_eq_mul_inv]
    exact OField.mul_lt_mul_right' hab (OField.inv_pos' hc)

## lean
Lean accepts the code.

## challenger
NO OBJECTION

Each axiom of `OField` is plainly a true statement about the real numbers, with `inv 0` set to any value. So the reals are a model, the hypotheses can be met, and my vacuity worry does not stand. The theorem's hypotheses (`a > b`, `0 < c`) and its four conclusions match Art. 246. Dropping the positivity of `a` and `b` only makes the result more general.

## critic
**Case against merging**

1. **The prover did not do what the challenger asked.**
   - The challenger asked for one concrete `OField` instance, for example the rationals, to show inside Lean that the hypotheses can be met.
   - The prover sent back the same code with only a prose reply. The claim "the reals are an instance" is still just a docstring, and Lean has checked no model of `OField`.
   - The challenger then withdrew on informal grounds ("each axiom is plainly a true statement about the real numbers"), not on any new evidence in the file.
   - I am not claiming the axioms are inconsistent. They are almost certainly satisfiable. My point is that the one issue raised in review was closed by assertion, not by code.
   - The prover's reason for refusing, that it would be "a large side development", does not hold up. An instance on a small structure such as `Rat` built from integer pairs, or even a check of the axioms on a finite test case, is a bounded task. Without it, nothing in the repository protects against a future edit adding an axiom that makes the class empty.

2. **The issue's "real and positive quantities" is stated only by proxy.**
   - Art. 245 fixes the domain as real positive quantities. The theorem instead ranges over a custom class whose link to the reals exists only in comments.
   - Dropping the positivity of `a` and `b` is a real generalization. But the faithfulness of the domain itself is never argued in code.
   - The statement also uses `OField.zero` rather than a numeral `0`. So a reader cannot see from the statement that "positive" means positive in the usual sense, rather than relative to an arbitrary distinguished element of an arbitrary carrier.
   - A reviewer has to trust the prose to accept that this is Art. 246 about real quantities, not a theorem about some abstract structure.

3. **The final file is not fit to merge as committed.**
   - The last submission puts the prover's review reply into the source as top-level comments: "Reply to the objection: no change to the code. The objection does not hold…", followed by a numbered rebuttal.
   - It then repeats the original header comment, so the file now carries duplicated, conversational text that belongs in the PR thread, not in the repository.
   - Merging would commit the argument instead of the artifact the argument promised. The file should at least be cleaned up and, per point 1, come with a checked instance before it lands.

## defender
**Rebuttal**

1. The issue asks only that Art. 246 be stated and proved, and Lean has checked both; an instance is not part of the task. Every `OField` axiom is a textbook ordered-field law that holds in ℝ by inspection, which is why the challenger withdrew, and an edit that empties the class later would face the same review.

2. `OField.zero` is not an arbitrary distinguished element: `zero_add` and `neg_add_cancel` make it the additive identity, and the order is tied to `+` and `*` by the axioms, so `zero < c` is ordinary positivity. Since ℝ is a model, the real-positive case of Art. 245–246 is a direct specialization of a strictly more general theorem.

3. I concede this point: the review reply and the duplicated header comment should not be committed. It is a comment-only cleanup that does not touch any declaration, statement or proof, so it is a fix to make before landing rather than a reason to reject the PR.

## supervisor
REVISE. Remove the review-reply comments and the duplicated header from the source; that text belongs in the PR thread, and the defender concedes this critic point, so it still stands. The statement itself is faithful: `OField` is a satisfiable ordered-field axiomatization that the reals model (with `inv 0` arbitrary), `OField.zero < c` is ordinary positivity, and dropping positivity of a and b only generalizes Art. 246. Keep every declaration and proof unchanged; a concrete instance is optional and not required for merge.

## prover
-- Lean core has no real numbers, so the theorem is stated for every ordered
-- field. The class below lists standard ordered field axioms, and the real
-- numbers form an ordered field, so the real case of Art. 246 is included.
-- Following Art. 245, `b < a` means that a exceeds b.
-- The hypothesis that a and b are positive is not needed, so it is left out.

universe u

/-- Standard axioms of an ordered field (the reals are an instance). -/
class OField (α : Type u) extends Add α, Mul α, Neg α, Sub α, Div α, LT α where
  zero : α
  one : α
  inv : α → α
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  zero_add : ∀ a : α, zero + a = a
  neg_add_cancel : ∀ a : α, -a + a = zero
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul : ∀ a : α, one * a = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  mul_inv_cancel : ∀ a : α, a ≠ zero → a * inv a = one
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  div_eq_mul_inv : ∀ a b : α, a / b = a * inv b
  lt_irrefl : ∀ a : α, ¬ a < a
  lt_trans : ∀ a b c : α, a < b → b < c → a < c
  lt_trichotomy : ∀ a b : α, a < b ∨ a = b ∨ b < a
  add_lt_add_right : ∀ a b c : α, a < b → a + c < b + c
  mul_pos : ∀ a b : α, zero < a → zero < b → zero < a * b
  zero_lt_one : zero < one

theorem OField.add_neg_cancel' {α : Type u} [OField α] (a : α) :
    a + -a = OField.zero := by
  rw [OField.add_comm]
  exact OField.neg_add_cancel a

theorem OField.add_zero' {α : Type u} [OField α] (a : α) :
    a + OField.zero = a := by
  rw [OField.add_comm]
  exact OField.zero_add a

theorem OField.zero_mul' {α : Type u} [OField α] (c : α) :
    (OField.zero : α) * c = OField.zero := by
  have h1 : (OField.zero : α) * c = OField.zero * c + OField.zero * c := by
    calc (OField.zero : α) * c = c * OField.zero := OField.mul_comm _ _
      _ = c * (OField.zero + OField.zero) := by rw [OField.zero_add]
      _ = c * OField.zero + c * OField.zero := OField.left_distrib _ _ _
      _ = OField.zero * c + OField.zero * c := by rw [OField.mul_comm c OField.zero]
  calc (OField.zero : α) * c = OField.zero + OField.zero * c := (OField.zero_add _).symm
    _ = (-(OField.zero * c) + OField.zero * c) + OField.zero * c := by
        rw [OField.neg_add_cancel]
    _ = -(OField.zero * c) + (OField.zero * c + OField.zero * c) := OField.add_assoc _ _ _
    _ = -(OField.zero * c) + OField.zero * c := by rw [← h1]
    _ = OField.zero := OField.neg_add_cancel _

theorem OField.mul_zero' {α : Type u} [OField α] (c : α) :
    c * OField.zero = OField.zero := by
  rw [OField.mul_comm]
  exact OField.zero_mul' c

theorem OField.right_distrib' {α : Type u} [OField α] (a b c : α) :
    (a + b) * c = a * c + b * c := by
  rw [OField.mul_comm (a + b) c, OField.left_distrib, OField.mul_comm c a,
    OField.mul_comm c b]

theorem OField.mul_lt_mul_right' {α : Type u} [OField α] {a b c : α}
    (h : a < b) (hc : OField.zero < c) : a * c < b * c := by
  have h1 : OField.zero < b + -a := by
    have := OField.add_lt_add_right a b (-a) h
    rw [OField.add_neg_cancel' a] at this
    exact this
  have h2 : OField.zero < (b + -a) * c := OField.mul_pos _ _ h1 hc
  have h3 := OField.add_lt_add_right _ _ (a * c) h2
  have e : (b + -a) * c + a * c = b * c := by
    rw [OField.right_distrib' b (-a) c, OField.add_assoc (b * c) ((-a) * c) (a * c),
      ← OField.right_distrib' (-a) a c, OField.neg_add_cancel, OField.zero_mul',
      OField.add_zero']
  rw [OField.zero_add (a * c), e] at h3
  exact h3

theorem OField.inv_pos' {α : Type u} [OField α] {c : α}
    (hc : OField.zero < c) : OField.zero < OField.inv c := by
  have hne : c ≠ OField.zero := by
    intro h
    rw [h] at hc
    exact OField.lt_irrefl _ hc
  have h1 := OField.mul_inv_cancel c hne
  rcases OField.lt_trichotomy OField.zero (OField.inv c) with h | h | h
  · exact h
  · exfalso
    rw [← h, OField.mul_zero'] at h1
    have := OField.zero_lt_one (α := α)
    rw [h1] at this
    exact OField.lt_irrefl _ this
  · exfalso
    have h2 := OField.add_lt_add_right _ _ (-(OField.inv c)) h
    rw [OField.add_neg_cancel' (OField.inv c), OField.zero_add] at h2
    have h3 := OField.mul_pos _ _ hc h2
    have e : c * -(OField.inv c) + OField.one = OField.zero := by
      rw [← h1, ← OField.left_distrib, OField.neg_add_cancel, OField.mul_zero']
    have h4 := OField.add_lt_add_right _ _ OField.one h3
    rw [OField.zero_add, e] at h4
    exact OField.lt_irrefl _ (OField.lt_trans _ _ _ h4 OField.zero_lt_one)

/-- Hall and Knight, Higher Algebra, Art. 246: if a > b and c is a positive
quantity, then a + c > b + c, a − c > b − c, ac > bc and a/c > b/c.
This is proved in every ordered field, the real numbers included. -/
theorem hk_art_246 {α : Type u} [OField α] (a b c : α)
    (hab : a > b) (hc : OField.zero < c) :
    a + c > b + c ∧ a - c > b - c ∧ a * c > b * c ∧ a / c > b / c := by
  refine ⟨OField.add_lt_add_right _ _ _ hab, ?_, OField.mul_lt_mul_right' hab hc, ?_⟩
  · rw [OField.sub_eq_add_neg, OField.sub_eq_add_neg]
    exact OField.add_lt_add_right _ _ _ hab
  · rw [OField.div_eq_mul_inv, OField.div_eq_mul_inv]
    exact OField.mul_lt_mul_right' hab (OField.inv_pos' hc)

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The prover answered every objection I raised. The leftover review-reply comments and the duplicated header are gone, and Lean accepts the cleaned file, whose declarations and proofs are the same as before. The statement of `hk_art_246` matches Art. 246: from `a > b` and `0 < c` it gives the four inequalities for adding, subtracting, multiplying and dividing by `c`. `OField` is a standard ordered-field axiom set that the reals satisfy, and leaving out the positivity of `a` and `b` only makes the result more general, so I cannot defend a further objection.

## critic
**Case against merging.** None of these points shows the theorem is wrong or unfaithful to Art. 246. They are the strongest remaining reservations, and I rate them as weak.

1. **The challenger's request for an instance was answered with prose, not code.**
   - The challenger asked for one concrete `OField` instance, so that Lean itself confirms the hypotheses can be met.
   - The prover never supplied one. The challenger withdrew on informal grounds ("each axiom is plainly a true statement about the real numbers").
   - That reasoning is correct. The reals satisfy every axiom, with `inv 0` arbitrary. So `hk_art_246` is not vacuous.
   - The supervisor also ruled an instance optional. So this is a gap in mechanical assurance, not an error. The only lasting cost is that nothing in the file guards against a future edit adding an axiom that empties the class.

2. **The "real positive quantities" domain is stated by proxy.**
   - Art. 245 fixes the domain as the reals. The theorem ranges over a custom class whose link to ℝ exists only in comments.
   - Positivity is written `OField.zero < c`, not with a numeral `0`.
   - The defender's rebuttal is sound on substance. `zero_add` and `neg_add_cancel` pin `zero` down as the additive identity, the order axioms tie `<` to `+` and `*`, and ℝ is a model. The real case of Art. 246 is therefore a direct specialization.
   - Dropping the positivity of `a` and `b` only generalizes the result. What remains here is a readability concern, not a faithfulness defect.

3. **The one blocking issue has been fixed.**
   - The review-reply comments and the duplicated header were the only point the defender conceded and the supervisor required to be fixed.
   - The final submission removes them, keeps every declaration and proof unchanged, and Lean accepts it.
   - So the prover did comply with the supervisor's REVISE, and this point no longer supports rejection.

**Conclusion.** My position is that the PR should not merge, and the best grounds I can give are points 1 and 2. In fairness, the final code states Art. 246 correctly, the proof checks, and every objection actually raised was either resolved or found non-blocking. I do not have a substantive defect to cite.

## defender
**Rebuttal**

1. The critic agrees that the reals satisfy every `OField` axiom, so `hk_art_246` is not vacuous, and the supervisor ruled an instance optional. A future edit that adds an axiom would itself go through review, and the issue asks for no instance, so a missing instance cannot block this PR.

2. The axioms force `OField.zero` to be the additive identity and tie `<` to `+` and `*`, so `OField.zero < c` means "c is positive." Because ℝ is a model, Art. 246 for real positive quantities follows directly by specialization, and the critic accepts that this is a readability matter, not a faithfulness defect.

3. This point supports merging: the only conceded issue, the leftover review-reply comments and the duplicated header, has been removed. Lean accepts the cleaned file with every declaration unchanged, so the supervisor's REVISE has been met.

**Conclusion.** The critic names no substantive defect. The statement is faithful to Art. 246, the proof checks, and the one required fix is done. The PR should merge.

## supervisor
**MERGE.** Lean accepts the final file, and `hk_art_246` matches Art. 246: from `a > b` and `OField.zero < c` it derives all four inequalities. `OField` is a consistent ordered-field axiomatization, since the reals satisfy every axiom with `inv 0` arbitrary, so the theorem is not vacuous, and dropping the positivity of a and b only generalizes it. The one conceded blocker, the leftover review comments, has been removed, and the critic's remaining points (no checked instance, positivity written as `OField.zero`) concern readability and extra assurance rather than correctness or faithfulness.
