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
