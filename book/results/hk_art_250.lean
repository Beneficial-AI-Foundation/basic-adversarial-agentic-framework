-- Revision following the supervisor's second REVISE.
-- * Docstring. The claim that the instance is missing "because only the prelude is available"
--   is withdrawn. The issue imposes no such rule, and my earlier comments were wrong to cite a
--   ban on `import`. The docstring now refers to the instance below and says that ℝ satisfies
--   the fifteen laws of `OrdField` by inspection only. The class has eighteen fields: three are
--   data (`zero`, `one`, `inv`) and fifteen are laws.
-- * Trial build. At the end of the file, `ratOrdField` is an `OrdField` instance for core
--   `Rat`, written without any `import`. Each law is tried against several likely core lemma
--   names, with `grind` as a fallback. If the checker accepts the file, the class is inhabited
--   and `hk_art_250` is not vacuous. If it rejects the file, the checker's error is the answer
--   to the supervisor's question, and I will report it in the thread.
-- * The rest is unchanged. The square-sum clauses need no square root, and the docstring
--   states how √(ab) is encoded.

class OrdField (α : Type) extends Add α, Mul α, Neg α, LT α where
  zero : α
  one : α
  inv : α → α
  addComm : ∀ x y : α, x + y = y + x
  addAssoc : ∀ x y z : α, x + y + z = x + (y + z)
  zeroAdd : ∀ x : α, zero + x = x
  addNeg : ∀ x : α, x + -x = zero
  mulComm : ∀ x y : α, x * y = y * x
  mulAssoc : ∀ x y z : α, x * y * z = x * (y * z)
  oneMul : ∀ x : α, one * x = x
  mulAdd : ∀ x y z : α, x * (y + z) = x * y + x * z
  mulInv : ∀ x : α, x ≠ zero → x * inv x = one
  ltIrrefl : ∀ x : α, ¬ x < x
  ltTrans : ∀ x y z : α, x < y → y < z → x < z
  ltTrichotomy : ∀ x y : α, x < y ∨ x = y ∨ y < x
  addLtAddRight : ∀ x y z : α, x < y → x + z < y + z
  mulPos : ∀ x y : α, zero < x → zero < y → zero < x * y
  zeroLtOne : zero < one

namespace OrdField

variable {α : Type} [OrdField α]

theorem addZero (x : α) : x + zero = x := by
  rw [addComm x zero, zeroAdd]

theorem negAdd (x : α) : -x + x = zero := by
  rw [addComm (-x) x]; exact addNeg x

theorem addLeftCancel {x y z : α} (h : z + x = z + y) : x = y :=
  calc x = zero + x := (zeroAdd x).symm
    _ = (-z + z) + x := by rw [negAdd]
    _ = -z + (z + x) := addAssoc _ _ _
    _ = -z + (z + y) := by rw [h]
    _ = (-z + z) + y := (addAssoc _ _ _).symm
    _ = y := by rw [negAdd, zeroAdd]

theorem mulZero (x : α) : x * zero = zero := by
  have h : x * zero + x * zero = x * zero + zero := by
    rw [← mulAdd, zeroAdd, addZero]
  exact addLeftCancel h

theorem mulOne (x : α) : x * one = x := by
  rw [mulComm x one, oneMul]

theorem addMul (x y z : α) : (x + y) * z = x * z + y * z := by
  rw [mulComm (x + y) z, mulAdd, mulComm z x, mulComm z y]

theorem addLeftComm (x y z : α) : x + (y + z) = y + (x + z) := by
  rw [← addAssoc x y z, addComm x y, addAssoc y x z]

theorem ltAddLeft {x y : α} (z : α) (h : x < y) : z + x < z + y := by
  rw [addComm z x, addComm z y]; exact addLtAddRight x y z h

theorem posOfLt {x y : α} (h : x < y) : zero < y + -x := by
  have h1 := addLtAddRight x y (-x) h
  rw [addNeg] at h1
  exact h1

theorem ltAsymm {x y : α} (h1 : x < y) (h2 : y < x) : False :=
  ltIrrefl x (ltTrans _ _ _ h1 h2)

theorem dbl {x y : α} (h : x < y) : x + x < y + y :=
  ltTrans _ _ _ (addLtAddRight x y x h) (ltAddLeft y h)

theorem negMulNeg (d : α) : (-d) * (-d) = d * d := by
  have h1 : d * (-d) + (-d) * (-d) = zero := by
    rw [mulComm d (-d), ← mulAdd, addNeg, mulZero]
  have h2 : d * (-d) + d * d = zero := by
    rw [addComm (d * (-d)) (d * d), ← mulAdd, addNeg, mulZero]
  exact addLeftCancel (h1.trans h2.symm)

theorem sqPos {d : α} (h : d ≠ zero) : zero < d * d := by
  rcases ltTrichotomy zero d with hd | hd | hd
  · exact mulPos d d hd hd
  · exact absurd hd.symm h
  · have hn : zero < -d := by
      have h1 := addLtAddRight d zero (-d) hd
      rw [addNeg, zeroAdd] at h1
      exact h1
    rw [← negMulNeg d]
    exact mulPos _ _ hn hn

theorem mulLtMulLeft {x y z : α} (hz : zero < z) (h : x < y) : z * x < z * y := by
  have h1 : zero < z * (y + -x) := mulPos _ _ hz (posOfLt h)
  rw [mulAdd] at h1
  have h2 : z * (-x) + z * x = zero := by rw [← mulAdd, negAdd, mulZero]
  have h3 := addLtAddRight _ _ (z * x) h1
  rw [zeroAdd, addAssoc, h2, addZero] at h3
  exact h3

theorem sqLt {x y : α} (hx : zero < x) (hy : zero < y) (h : x < y) : x * x < y * y :=
  ltTrans _ _ _ (mulLtMulLeft hx h) (by rw [mulComm x y]; exact mulLtMulLeft hy h)

theorem sqInj {x y : α} (hx : zero < x) (hy : zero < y) (h : x * x = y * y) : x = y := by
  rcases ltTrichotomy x y with hl | hl | hl
  · have h1 := sqLt hx hy hl
    rw [h] at h1
    exact absurd h1 (ltIrrefl _)
  · exact hl
  · have h1 := sqLt hy hx hl
    rw [h] at h1
    exact absurd h1 (ltIrrefl _)

theorem twoPos : (zero : α) < one + one := by
  have h1 : (zero : α) < one := zeroLtOne
  have h2 := addLtAddRight _ _ one h1
  rw [zeroAdd] at h2
  exact ltTrans _ _ _ h1 h2

theorem twoNe : (one + one : α) ≠ zero := by
  intro e
  have h := twoPos (α := α)
  rw [e] at h
  exact ltIrrefl _ h

theorem halfAdd (x : α) : x * inv (one + one) + x * inv (one + one) = x :=
  calc x * inv (one + one) + x * inv (one + one)
        = (x * inv (one + one)) * one + (x * inv (one + one)) * one := by
          rw [mulOne (x * inv (one + one))]
    _ = (x * inv (one + one)) * (one + one) := (mulAdd _ _ _).symm
    _ = x * ((one + one) * inv (one + one)) := by
          rw [mulAssoc, mulComm (inv (one + one)) (one + one)]
    _ = x := by rw [mulInv (one + one : α) twoNe, mulOne]

/-- Hall & Knight, *Higher Algebra*, Art. 250, stated for positive quantities `a`, `b` of an
arbitrary ordered field `α`. The axioms are those of `OrdField`: three data fields and
fifteen laws. A Lean instance of `OrdField` for core `Rat` is given at the end of the file
(`ratOrdField`), which shows that the class is inhabited. ℝ satisfies the fifteen laws by
inspection; no Lean instance for ℝ is given.

* `a² + b² > 2ab` when `a ≠ b`, with equality when `a = b`. Here `2ab` is written `ab + ab`.
  These two clauses need no square root.
* Arithmetic mean versus geometric mean. √(ab) is encoded as any `s > 0` with
  `s * s = a * b`. In ℝ such an `s` exists and is unique, and it is exactly √(ab). For every
  such `s`, the arithmetic mean `(a + b)/2 = (a + b) * inv 2` is greater than `s` when
  `a ≠ b`, and equal to `s` when `a = b`. -/
theorem _root_.hk_art_250 {α : Type} [OrdField α] (a b : α)
    (ha : zero < a) (hb : zero < b) :
    (a ≠ b → a * b + a * b < a * a + b * b) ∧
    (a = b → a * a + b * b = a * b + a * b) ∧
    (∀ s : α, zero < s → s * s = a * b →
      (a ≠ b → s < (a + b) * inv (one + one)) ∧
      (a = b → s = (a + b) * inv (one + one))) := by
  have claim1 : a ≠ b → a * b + a * b < a * a + b * b := by
    intro h
    have hd : a + -b ≠ zero := by
      intro e
      apply h
      calc a = a + (-b + b) := by rw [negAdd, addZero]
        _ = (a + -b) + b := (addAssoc _ _ _).symm
        _ = b := by rw [e, zeroAdd]
    have hp := sqPos hd
    have hq : (a + -b) * (a + -b) + (a * b + a * b) = a * a + b * b := by
      have p0 : a * (-b) + a * b = zero := by rw [← mulAdd, negAdd, mulZero]
      rw [addMul, mulAdd, mulAdd, mulComm (-b) a, negMulNeg b]
      calc _ = (a * a + b * b) + ((a * (-b) + a * b) + (a * (-b) + a * b)) := by
            simp only [addAssoc, addComm, addLeftComm]
        _ = a * a + b * b := by rw [p0, addZero, addZero]
    have h1 := addLtAddRight _ _ (a * b + a * b) hp
    rw [zeroAdd, hq] at h1
    exact h1
  have hh : (zero : α) < inv (one + one) := by
    rcases ltTrichotomy (zero : α) (inv (one + one)) with h | h | h
    · exact h
    · exfalso
      have h3 := mulInv (one + one : α) twoNe
      rw [← h, mulZero] at h3
      have h4 : (zero : α) < one := zeroLtOne
      rw [← h3] at h4
      exact ltIrrefl _ h4
    · exfalso
      have h3 := mulLtMulLeft (twoPos (α := α)) h
      rw [mulInv (one + one : α) twoNe, mulZero] at h3
      exact ltAsymm h3 zeroLtOne
  have hab : zero < a + b := by
    have h1 := ltAddLeft a hb
    rw [addZero] at h1
    exact ltTrans _ _ _ ha h1
  refine ⟨claim1, ?_, ?_⟩
  · intro h
    rw [h]
  · intro s hs hss
    refine ⟨?_, ?_⟩
    · intro h
      have key : ∀ m : α, zero < m → m + m = a + b → s < m := by
        intro m hm0 hmm
        have hmsq : a * b < m * m := by
          have e1 : (m + m) * (m + m) = (m * m + m * m) + (m * m + m * m) := by
            rw [addMul, mulAdd]
          have e2 : (a + b) * (a + b) = (a * a + b * b) + (a * b + a * b) := by
            rw [addMul, mulAdd, mulAdd, mulComm b a]
            simp only [addAssoc, addComm, addLeftComm]
          have c1 := claim1 h
          have c2 : (a * b + a * b) + (a * b + a * b) < (m * m + m * m) + (m * m + m * m) := by
            rw [← e1, hmm, e2]
            exact addLtAddRight _ _ (a * b + a * b) c1
          rcases ltTrichotomy (a * b) (m * m) with h3 | h3 | h3
          · exact h3
          · exfalso
            rw [h3] at c2
            exact ltIrrefl _ c2
          · exfalso
            exact ltAsymm (dbl (dbl h3)) c2
        rcases ltTrichotomy s m with h4 | h4 | h4
        · exact h4
        · exfalso
          rw [← h4, hss] at hmsq
          exact ltIrrefl _ hmsq
        · exfalso
          have h5 := sqLt hm0 hs h4
          rw [hss] at h5
          exact ltAsymm h5 hmsq
      exact key _ (mulPos _ _ hab hh) (halfAdd _)
    · intro h
      subst h
      rw [addMul, halfAdd]
      exact sqInj hs ha hss

end OrdField

/-- Trial model: core `Rat` is an `OrdField`, so the class is inhabited. -/
instance ratOrdField : OrdField Rat where
  toAdd := inferInstance
  toMul := inferInstance
  toNeg := inferInstance
  toLT := inferInstance
  zero := 0
  one := 1
  inv := fun x => x⁻¹
  addComm := by
    intro x y
    show x + y = y + x
    first | exact Rat.add_comm x y | grind
  addAssoc := by
    intro x y z
    show x + y + z = x + (y + z)
    first | exact Rat.add_assoc x y z | grind
  zeroAdd := by
    intro x
    show 0 + x = x
    first | exact Rat.zero_add x | grind
  addNeg := by
    intro x
    show x + -x = 0
    first
      | exact Rat.add_neg_cancel x
      | (rw [Rat.add_comm]; exact Rat.neg_add_cancel x)
      | grind
  mulComm := by
    intro x y
    show x * y = y * x
    first | exact Rat.mul_comm x y | grind
  mulAssoc := by
    intro x y z
    show x * y * z = x * (y * z)
    first | exact Rat.mul_assoc x y z | grind
  oneMul := by
    intro x
    show 1 * x = x
    first | exact Rat.one_mul x | grind
  mulAdd := by
    intro x y z
    show x * (y + z) = x * y + x * z
    first | exact Rat.mul_add x y z | grind
  mulInv := by
    intro x h
    have h' : x ≠ 0 := h
    show x * x⁻¹ = 1
    first
      | exact Rat.mul_inv_cancel x h'
      | exact Rat.mul_inv_cancel h'
      | grind
  ltIrrefl := by
    intro x
    show ¬ x < x
    first | exact Rat.lt_irrefl x | exact Rat.lt_irrefl | grind
  ltTrans := by
    intro x y z h1 h2
    have h1' : x < y := h1
    have h2' : y < z := h2
    show x < z
    first | exact Rat.lt_trans h1' h2' | grind
  ltTrichotomy := by
    intro x y
    show x < y ∨ x = y ∨ y < x
    first | exact Rat.lt_trichotomy x y | grind
  addLtAddRight := by
    intro x y z h
    have h' : x < y := h
    show x + z < y + z
    first
      | exact Rat.add_lt_add_right h' z
      | exact (Rat.add_lt_add_right).mpr h'
      | grind
  mulPos := by
    intro x y hx hy
    have hx' : (0 : Rat) < x := hx
    have hy' : (0 : Rat) < y := hy
    show 0 < x * y
    first | exact Rat.mul_pos hx' hy' | grind
  zeroLtOne := by
    show (0 : Rat) < 1
    first | decide | exact Rat.zero_lt_one | grind
