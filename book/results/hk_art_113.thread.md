## issue
Issue #113. Art. 113, The Theory of Quadratic Equations
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter IX (The Theory of Quadratic Equations), Art. 113.
The book prints the following text.
111. After suitable reduction every quadratic equation may be written in the form ax^2 + bx + c = 0 ......(1), and the solution of the equation is x = (−b ± √(b^2 − 4ac))/(2a) ......(2).
In Art. 111 let the two roots in (2) be denoted by α and β, so that α = (−b + √(b^2 − 4ac))/(2a), β = (−b − √(b^2 − 4ac))/(2a); then we have the following results :
(1) If b^2 − 4ac (the quantity under the radical) is positive, α and β are real and unequal. (2) If b^2 − 4ac is zero, α and β are real and equal, each reducing in this case to −b/(2a). (3) If b^2 − 4ac is negative, α and β are imaginary and unequal. (4) If b^2 − 4ac is a perfect square, α and β are rational and unequal.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_113.

## prover
-- Lean core has no real or complex numbers, so this works over `Int`. Any equation with rational
-- coefficients becomes one with integer coefficients after clearing denominators. A rational
-- number x is written as a pair p/q with q ≠ 0.
-- * Case (1), "real": we show that a·(ax²+bx+c) changes sign twice along the points p/(2a). The
--   intermediate value theorem then gives two distinct real roots, but that step is not proved here.
-- * Case (3), "imaginary": we show only that the trinomial has no rational root. The
--   inequality 0 < a·f also holds for real x by the same identity, but this code does not prove it.
-- * Case (4): zero is also a perfect square, yet it gives equal roots. So we assume D ≠ 0, as the book does tacitly.

/-- The homogenised trinomial `a p² + b p q + c q²`. For `q ≠ 0` it equals `q²·(a x² + b x + c)` at `x = p/q`. -/
def hkQuad (a b c p q : Int) : Int := a * p * p + b * p * q + c * q * q

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

theorem hk_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have h2 := Int.mul_nonneg h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_sq_pos (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  by_cases h : 0 < x
  · exact Int.mul_pos h h
  · have h' : 0 < -x := by omega
    have h2 := Int.mul_pos h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_key (a b c p q : Int) :
    4 * (a * hkQuad a b c p q)
      = (2 * a * p + b * q) * (2 * a * p + b * q) - hkDisc a b c * (q * q) := by
  unfold hkQuad hkDisc; grind

theorem hk_shift (a b c t : Int) :
    a * hkQuad a b c (-b + t) (2 * a) = a * a * (t * t - hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

theorem hk_root (a b c t : Int) :
    hkQuad a b c (-b + t) (2 * a) = a * (t * t - hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

theorem hk_vertex (a b c : Int) :
    a * hkQuad a b c (-b) (2 * a) = -(a * a * hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

theorem hk_vertex' (a b c : Int) :
    hkQuad a b c (-b) (2 * a) = -(a * hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

/-- Hall and Knight, Art. 113. Take `a x² + b x + c = 0` with integer coefficients and `a ≠ 0`,
and put `D = b² − 4ac`. The roots are `α, β = (−b ± √D)/(2a)`.
(1) If `D > 0`, then `a·(ax²+bx+c)` is negative at `x = −b/(2a)` and positive at a point on
each side of it. So the roots are real and unequal.
(2) If `D = 0`, then `4a(ax²+bx+c) = (2ax+b)²`, so both roots reduce to `−b/(2a)`. It is a
root, and it is the only rational root.
(3) If `D < 0`, then `D ≠ 0`, so the roots are unequal. Also `a·(ax²+bx+c) > 0` at every
rational `x`, so no rational number is a root. Imaginary roots are not shown here.
(4) If `D = k²` with `D ≠ 0`, then `(−b + k)/(2a)` and `(−b − k)/(2a)` are rational roots,
and they are unequal. -/
theorem hk_art_113 (a b c : Int) (ha : a ≠ 0) :
    (0 < hkDisc a b c →
      ∃ p₁ p₀ p₂ : Int, p₁ < p₀ ∧ p₀ < p₂ ∧
        0 < a * hkQuad a b c p₁ (2 * a) ∧
        a * hkQuad a b c p₀ (2 * a) < 0 ∧
        0 < a * hkQuad a b c p₂ (2 * a)) ∧
    (hkDisc a b c = 0 →
      hkQuad a b c (-b) (2 * a) = 0 ∧
      (∀ p q : Int, 4 * (a * hkQuad a b c p q) = (2 * a * p + b * q) * (2 * a * p + b * q)) ∧
      (∀ p q : Int, q ≠ 0 → hkQuad a b c p q = 0 → 2 * a * p + b * q = 0)) ∧
    (hkDisc a b c < 0 →
      hkDisc a b c ≠ 0 ∧ ∀ p q : Int, q ≠ 0 → 0 < a * hkQuad a b c p q) ∧
    (∀ k : Int, hkDisc a b c = k * k → hkDisc a b c ≠ 0 →
      hkQuad a b c (-b + k) (2 * a) = 0 ∧
      hkQuad a b c (-b - k) (2 * a) = 0 ∧
      -b + k ≠ -b - k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hD
    have hD2 : (hkDisc a b c + 1) * (hkDisc a b c + 1)
        = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
    have hD3 : (-(hkDisc a b c + 1)) * (-(hkDisc a b c + 1))
        = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
    have hsq := hk_sq_nonneg (hkDisc a b c)
    have haa := hk_sq_pos a ha
    refine ⟨-b + -(hkDisc a b c + 1), -b, -b + (hkDisc a b c + 1),
      by omega, by omega, ?_, ?_, ?_⟩
    · rw [hk_shift]
      exact Int.mul_pos haa (by omega)
    · rw [hk_vertex]
      have := Int.mul_pos haa hD
      omega
    · rw [hk_shift]
      exact Int.mul_pos haa (by omega)
  · intro hD
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_vertex', hD, Int.mul_zero, Int.neg_zero]
    · intro p q
      have h := hk_key a b c p q
      rw [hD, Int.zero_mul, Int.sub_zero] at h
      exact h
    · intro p q _ hf
      have h := hk_key a b c p q
      rw [hD, Int.zero_mul, Int.sub_zero, hf] at h
      by_cases hs : 2 * a * p + b * q = 0
      · exact hs
      · have := hk_sq_pos _ hs
        omega
  · intro hD
    refine ⟨by omega, ?_⟩
    intro p q hq
    have hK := hk_key a b c p q
    have h1 := hk_sq_nonneg (2 * a * p + b * q)
    have hqq := hk_sq_pos q hq
    have h2 : 0 < -hkDisc a b c * (q * q) := Int.mul_pos (by omega) hqq
    rw [Int.neg_mul] at h2
    omega
  · intro k hk hD0
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, Int.mul_zero] at hk
      exact hD0 hk
    refine ⟨?_, ?_, by omega⟩
    · rw [hk_root, ← hk, Int.sub_self, Int.mul_zero]
    · have e : -b - k = -b + -k := by omega
      rw [e, hk_root, Int.neg_mul_neg, ← hk, Int.sub_self, Int.mul_zero]

## lean
Lean accepts the code.

## challenger
OBJECTION: The theorem never states the article's claims about α and β; it substitutes proxies whose link to those claims the code admits it does not prove. In case (1), "real and unequal" is replaced by two sign changes of a·hkQuad on the grid p/(2a), and the intermediate value step that would give two distinct real roots is missing. In case (3), "imaginary and unequal" becomes the tautology D ≠ 0 plus "no rational root", which says nothing about whether the roots are non-real or about the roots at all. Since α = (−b+√D)/(2a) and β = (−b−√D)/(2a) are never defined, the Lean statement is strictly weaker than the prose in cases (1) and (3), and no faithfulness proof bridges the gap.

## prover
-- Reply to the objection. The objection is right. The earlier statement never defined α and β,
-- so the code now defines them.
-- Lean core has no ℝ or ℂ. So the roots live in an arbitrary field `K` (core class
-- `Lean.Grind.Field`) with characteristic zero, given an element `s` with `s * s = D`, where
-- `D = b² − 4ac`. In that field `α = (−b + s)/(2a)` and `β = (−b − s)/(2a)`, as in Art. 111.
-- * Case (1), real: if `D > 0`, take `K = ℝ` and `s = √D`. Then α and β are real roots and
--   α ≠ β. The step "√D exists in ℝ for D > 0" comes from outside the code, because ℝ is not
--   in core. The integer sign-change certificate from the first version is kept as a
--   self-contained check.
-- * Case (3), imaginary: take `K = ℂ` with `s * s = D`. There α and β are unequal roots.
--   Also, in any field where no square is a negative integer (such as ℝ), the equation has no
--   root at all, so α and β are not real.
-- * Case (2): `D = 0` forces `s = 0`, so α = β = −b/(2a).
-- * Case (4): `D = k²` with `D ≠ 0` makes α and β quotients of integers, and they are unequal.

def hkQuad (a b c p q : Int) : Int := a * p * p + b * p * q + c * q * q

def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

theorem hk_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have h2 := Int.mul_nonneg h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_sq_pos (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  by_cases h : 0 < x
  · exact Int.mul_pos h h
  · have h' : 0 < -x := by omega
    have h2 := Int.mul_pos h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_shift (a b c t : Int) :
    a * hkQuad a b c (-b + t) (2 * a) = a * a * (t * t - hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

theorem hk_vertex (a b c : Int) :
    a * hkQuad a b c (-b) (2 * a) = -(a * a * hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

section HKField
universe u
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)`, where `s` is a square root of the discriminant. -/
def hkAlpha (a b : Int) (s : K) : K := (-(b : K) + s) / (2 * (a : K))

/-- The root `β = (−b − s)/(2a)`. -/
def hkBeta (a b : Int) (s : K) : K := (-(b : K) - s) / (2 * (a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`. -/
def hkRoot (a b c : Int) (x : K) : Prop := (a : K) * x * x + (b : K) * x + (c : K) = 0

theorem hk_cast_add (x y : Int) : ((x + y : Int) : K) = (x : K) + (y : K) := by
  first | rw [Lean.Grind.Ring.intCast_add] | grind

theorem hk_cast_neg (x : Int) : ((-x : Int) : K) = -(x : K) := by
  first | rw [Lean.Grind.Ring.intCast_neg] | grind

theorem hk_cast_mul (x y : Int) : ((x * y : Int) : K) = (x : K) * (y : K) := by
  first | rw [Lean.Grind.Ring.intCast_mul] | grind

theorem hk_cast_sub (x y : Int) : ((x - y : Int) : K) = (x : K) - (y : K) := by
  first
  | rw [Lean.Grind.Ring.intCast_sub]
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)

theorem hk_cast_zero : ((0 : Int) : K) = 0 := by
  first
  | rw [Lean.Grind.Ring.intCast_zero]
  | (have h := hk_cast_add (K := K) 0 0
     rw [Int.add_zero] at h
     grind)

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first | rw [Lean.Grind.Field.div_eq_mul_inv] | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first | exact Lean.Grind.Field.mul_inv_cancel hx | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    grind

theorem hk_disc_cast (a b c : Int) :
    ((hkDisc a b c : Int) : K) = (b : K) * (b : K) - 4 * (a : K) * (c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (a : K) ≠ 0 := by
  intro h
  have h2 : ((a + a : Int) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (n : K) = 0 → n = 0)
    (s : K) (hs : s * s = ((hkDisc a b c : Int) : K)) : hkRoot a b c (hkAlpha a b s) := by
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  rw [hk_disc_cast] at hs
  unfold hkRoot hkAlpha
  rw [hk_div]
  generalize (2 * (a : K))⁻¹ = w at hinv ⊢
  grind

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (n : K) = 0 → n = 0)
    (s : K) (hs : s * s = ((hkDisc a b c : Int) : K)) : hkRoot a b c (hkBeta a b s) := by
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  rw [hk_disc_cast] at hs
  unfold hkRoot hkBeta
  rw [hk_div]
  generalize (2 * (a : K))⁻¹ = w at hinv ⊢
  grind

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (n : K) = 0 → n = 0)
    (s : K) (hs : s * s = ((hkDisc a b c : Int) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  unfold hkAlpha hkBeta at h
  rw [hk_div, hk_div] at h
  generalize (2 * (a : K))⁻¹ = w at hinv h
  have hs0 : s = 0 := by grind
  apply hD
  apply hchar
  rw [← hs, hs0]
  grind

theorem hk_double (a b c : Int) (s : K) (hs : s * s = ((hkDisc a b c : Int) : K))
    (hD : hkDisc a b c = 0) :
    hkAlpha a b s = -(b : K) / (2 * (a : K)) ∧ hkBeta a b s = -(b : K) / (2 * (a : K)) := by
  rw [hD, hk_cast_zero] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  unfold hkAlpha hkBeta
  constructor <;> congr 1 <;> grind

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = ((hkDisc a b c : Int) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (p₁ : K) / (q : K) ∧
      hkBeta a b s = (p₂ : K) / (q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hf : (s - (k : K)) * (s + (k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩ <;>
      simp only [hkAlpha, hkBeta, hk_cast_add, hk_cast_sub, hk_cast_neg] <;>
      congr 1 <;> grind
  · refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩ <;>
      simp only [hkAlpha, hkBeta, hk_cast_add, hk_cast_sub, hk_cast_neg] <;>
      congr 1 <;> grind

theorem hk_no_root (a b c : Int) (hreal : ∀ y : K, ∀ n : Int, n < 0 → y * y ≠ (n : K))
    (hD : hkDisc a b c < 0) (x : K) : ¬ hkRoot a b c x := by
  intro h
  unfold hkRoot at h
  apply hreal (2 * (a : K) * x + (b : K)) (hkDisc a b c) hD
  rw [hk_disc_cast]
  grind

end HKField

/-- Hall and Knight, Art. 113. Take `a x² + b x + c = 0` with integer coefficients and `a ≠ 0`,
and put `D = b² − 4ac`. In any characteristic-zero field `K` with `s * s = D`, the roots are
`α = (−b + s)/(2a)` and `β = (−b − s)/(2a)`. Both are roots, and:
(1) If `D > 0`, then `α ≠ β`. With `K = ℝ` and `s = √D`, they are real and unequal. An integer
sign-change certificate is also given.
(2) If `D = 0`, then `α = β = −b/(2a)`.
(3) If `D < 0`, then `α ≠ β` (in `ℂ`). In no field where no square is a negative integer
(such as `ℝ`) does the equation have a root, so `α` and `β` are imaginary.
(4) If `D = k²` with `D ≠ 0`, then `α` and `β` are quotients of integers, and they are unequal. -/
theorem hk_art_113 (a b c : Int) (ha : a ≠ 0) :
    (∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (n : K) = 0 → n = 0) →
      ∀ s : K, s * s = ((hkDisc a b c : Int) : K) →
        hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
        (0 < hkDisc a b c → hkAlpha a b s ≠ hkBeta a b s) ∧
        (hkDisc a b c = 0 →
          hkAlpha a b s = -(b : K) / (2 * (a : K)) ∧
          hkBeta a b s = -(b : K) / (2 * (a : K))) ∧
        (hkDisc a b c < 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
        (∀ k : Int, hkDisc a b c = k * k → hkDisc a b c ≠ 0 →
          (∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (p₁ : K) / (q : K) ∧
            hkBeta a b s = (p₂ : K) / (q : K)) ∧
          hkAlpha a b s ≠ hkBeta a b s)) ∧
    (hkDisc a b c < 0 → ∀ (K : Type) [Lean.Grind.Field K],
      (∀ y : K, ∀ n : Int, n < 0 → y * y ≠ (n : K)) → ∀ x : K, ¬ hkRoot a b c x) ∧
    (0 < hkDisc a b c →
      ∃ p₁ p₀ p₂ : Int, p₁ < p₀ ∧ p₀ < p₂ ∧
        0 < a * hkQuad a b c p₁ (2 * a) ∧
        a * hkQuad a b c p₀ (2 * a) < 0 ∧
        0 < a * hkQuad a b c p₂ (2 * a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs (by omega), fun hD => hk_double a b c s hs hD,
      fun hD => hk_ne a b c ha hchar s hs (by omega),
      fun k hk hD0 => ⟨hk_rational a b c ha s hs k hk, hk_ne a b c ha hchar s hs hD0⟩⟩
  · intro hD K inst hreal x
    exact hk_no_root a b c hreal hD x
  · intro hD
    have hsq := hk_sq_nonneg (hkDisc a b c)
    have haa := hk_sq_pos a ha
    refine ⟨-b + -(hkDisc a b c + 1), -b, -b + (hkDisc a b c + 1),
      by omega, by omega, ?_, ?_, ?_⟩
    · rw [hk_shift]
      have e : (-(hkDisc a b c + 1)) * (-(hkDisc a b c + 1))
          = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
      exact Int.mul_pos haa (by omega)
    · rw [hk_vertex]
      have := Int.mul_pos haa hD
      omega
    · rw [hk_shift]
      have e : (hkDisc a b c + 1) * (hkDisc a b c + 1)
          = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
      exact Int.mul_pos haa (by omega)

## lean
The Lean check failed. Lean rejects the code. <stdin>:49:41: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:49:61: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:52:40: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:52:60: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:55:43: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:55:61: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:55:75: error: Type mismatch
  c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:57:34: error: Type mismatch
  x + y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:57:56: error: Type mismatch
  x
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:57:66: error: Type mismatch
  y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:60:32: error: Type mismatch
  -x
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:60:52: error: Type mismatch
  x
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:63:34: error: Type mismatch
  x * y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:63:56: error: Type mismatch
  x
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:63:66: error: Type mismatch
  y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:66:34: error: Type mismatch
  x - y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:66:56: error: Type mismatch
  x
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:66:66: error: Type mismatch
  y
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:71:23: error: Type mismatch
  0
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:74:27: error: Invalid argument name `K` for function `hk_cast_add`

Hint: Perhaps you meant one of the following parameter names:
  • `x`: K̵x̲
  • `y`: K̵y̲
<stdin>:71:46: error: unsolved goals
⊢ sorry = 0
<stdin>:92:4: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:92:33: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:92:43: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:92:57: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:92:67: error: Type mismatch
  c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:98:50: error: Type mismatch
  n
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:99:8: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:101:29: error(lean.unknownIdentifier): Unknown identifier `K`
<stdin>:99:23: error: unsolved goals
a : Int
hchar : ∀ (n : Int), sorry = 0 → n = 0
ha : a ≠ 0
h : 2 * sorry = 0
h2 : sorry = 0
⊢ False
<stdin>:105:69: error: Type mismatch
  n
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:106:26: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:115:68: error: Type mismatch
  n
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:116:26: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:125:61: error: Type mismatch
  n
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:126:26: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:140:54: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:142:21: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:142:36: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:142:63: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:142:78: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:150:18: error: Type mismatch
  hkDisc a b c
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:151:45: error: Type mismatch
  p₁
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:151:56: error: Type mismatch
  q
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:152:21: error: Type mismatch
  p₂
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:152:32: error: Type mismatch
  q
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:163:78: error: Type mismatch
  n
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:167:19: error: Type mismatch
  a
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:167:33: error: Type mismatch
  b
has type
  Int
of sort `Type` but is expected to have type
  K
of sort `Type u`
<stdin>:183:52: error: Type mismatch
  n
has type
  Int
but is expected to have type
  K
<stdin>:184:23: error: Type mismatch
  hkDisc a b c
has type
  Int
but is expected to have type
  K
<stdin>:188:27: error: Type mismatch
  b
has type
  Int
but is expected to have type
  K
<stdin>:188:42: error: Type mismatch
  a
has type
  Int
but is expected to have type
  K
<stdin>:189:26: error: Type mismatch
  b
has type
  Int
but is expected to have type
  K
<stdin>:189:41: error: Type mismatch
  a
has type
  Int
but is expected to have type
  K
<stdin>:192:52: error: Type mismatch
  p₁
has type
  Int
but is expected to have type
  K
<stdin>:192:63: error: Type mismatch
  q
has type
  Int
but is expected to have type
  K
<stdin>:193:27: error: Type mismatch
  p₂
has type
  Int
but is expected to have type
  K
<stdin>:193:38: error: Type mismatch
  q
has type
  Int
but is expected to have type
  K
<stdin>:196:43: error: Type mismatch
  n
has type
  Int
but is expected to have type
  K
'hk_art_113' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]


## challenger
OBJECTION: The Lean check failed, so this pull request proves nothing, and `hk_art_113` depends on `sorryAx`. Every cast `(b : K)`, `(n : K)` and `((hkDisc a b c : Int) : K)` is rejected with "Type mismatch Int … expected K", because core Lean registers no `Int → K` coercion for a `Lean.Grind.Field K`. You must write `Int.cast b` or `(IntCast.intCast b : K)` explicitly, and `hk_cast_add (K := K)` also fails because `K` is not a named parameter there. Even after a repair, the field part only states that α and β are real and unequal when some `s` with `s * s = D` exists in a real field, and the code never proves such an `s` exists, so the substantive claim of case (1) still rests on an unproved assumption.

## prover
-- Reply to the review.
-- * Compile errors: core Lean has no coercion `Int → K` for a `Lean.Grind.Field K`. Every cast
--   is now written out as `(Int.cast n : K)`. The cast lemmas no longer use named arguments.
-- * The case (1) point does not hold as a defect of this code. Core Lean has no ℝ, so no proof
--   inside core can build `√D`. The code proves the following.
--   - In every characteristic-zero field `K` that has an `s` with `s * s = D`,
--     α = (−b+s)/(2a) and β = (−b−s)/(2a) are roots, and α ≠ β when D > 0.
--   - With integers only, `a·(ax²+bx+c)` changes sign twice along the points p/(2a).
--   That `√D` exists in ℝ for D > 0 comes from the completeness of ℝ. The book also takes
--   this fact for granted, and core Lean cannot state it.

/-- The homogenised trinomial `a p² + b p q + c q²`. -/
def hkQuad (a b c p q : Int) : Int := a * p * p + b * p * q + c * q * q

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

theorem hk_sq_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have h2 := Int.mul_nonneg h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_sq_pos (x : Int) (hx : x ≠ 0) : 0 < x * x := by
  by_cases h : 0 < x
  · exact Int.mul_pos h h
  · have h' : 0 < -x := by omega
    have h2 := Int.mul_pos h' h'
    rw [Int.neg_mul_neg] at h2
    exact h2

theorem hk_shift (a b c t : Int) :
    a * hkQuad a b c (-b + t) (2 * a) = a * a * (t * t - hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

theorem hk_vertex (a b c : Int) :
    a * hkQuad a b c (-b) (2 * a) = -(a * a * hkDisc a b c) := by
  unfold hkQuad hkDisc; grind

section HKField
universe u
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)`. -/
def hkAlpha (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) + s) / (2 * (Int.cast a : K))

/-- The root `β = (−b − s)/(2a)`. -/
def hkBeta (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) - s) / (2 * (Int.cast a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`. -/
def hkRoot (a b c : Int) (x : K) : Prop :=
  (Int.cast a : K) * x * x + (Int.cast b : K) * x + (Int.cast c : K) = 0

theorem hk_cast_add (x y : Int) :
    (Int.cast (x + y) : K) = (Int.cast x : K) + (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_add x y
  | exact Lean.Grind.Ring.intCast_add _ _
  | rw [Lean.Grind.Ring.intCast_add]
  | simp [Lean.Grind.Ring.intCast_add]
  | grind

theorem hk_cast_neg (x : Int) : (Int.cast (-x) : K) = -(Int.cast x : K) := by
  first
  | exact Lean.Grind.Ring.intCast_neg x
  | exact Lean.Grind.Ring.intCast_neg _
  | rw [Lean.Grind.Ring.intCast_neg]
  | simp [Lean.Grind.Ring.intCast_neg]
  | grind

theorem hk_cast_mul (x y : Int) :
    (Int.cast (x * y) : K) = (Int.cast x : K) * (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_mul x y
  | exact Lean.Grind.Ring.intCast_mul _ _
  | rw [Lean.Grind.Ring.intCast_mul]
  | simp [Lean.Grind.Ring.intCast_mul]
  | grind

theorem hk_cast_sub (x y : Int) :
    (Int.cast (x - y) : K) = (Int.cast x : K) - (Int.cast y : K) := by
  first
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)
  | exact Lean.Grind.Ring.intCast_sub x y
  | grind

theorem hk_cast_zero : (Int.cast (0 : Int) : K) = 0 := by
  have h := hk_cast_add (K := K) 0 0
  rw [Int.add_zero] at h
  grind

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first | exact Lean.Grind.Field.div_eq_mul_inv x y | rw [Lean.Grind.Field.div_eq_mul_inv] | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first | exact Lean.Grind.Field.mul_inv_cancel hx | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    grind

theorem hk_disc_cast (a b c : Int) :
    (Int.cast (hkDisc a b c) : K)
      = (Int.cast b : K) * (Int.cast b : K) - 4 * (Int.cast a : K) * (Int.cast c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (Int.cast a : K) ≠ 0 := by
  intro h
  have h2 : (Int.cast (a + a) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkAlpha a b s) := by
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  rw [hk_disc_cast] at hs
  unfold hkRoot hkAlpha
  rw [hk_div]
  generalize (2 * (Int.cast a : K))⁻¹ = w at hinv ⊢
  grind

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkBeta a b s) := by
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  rw [hk_disc_cast] at hs
  unfold hkRoot hkBeta
  rw [hk_div]
  generalize (2 * (Int.cast a : K))⁻¹ = w at hinv ⊢
  grind

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have hd := hk_two_a_ne a hchar ha
  have hinv := hk_inv hd
  unfold hkAlpha hkBeta at h
  rw [hk_div, hk_div] at h
  generalize (2 * (Int.cast a : K))⁻¹ = w at hinv h
  have hs0 : s = 0 := by grind
  apply hD
  apply hchar
  rw [← hs, hs0]
  grind

theorem hk_double (a b c : Int) (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K))
    (hD : hkDisc a b c = 0) :
    hkAlpha a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) ∧
    hkBeta a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) := by
  rw [hD, hk_cast_zero] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  have e1 : -(Int.cast b : K) + 0 = -(Int.cast b : K) := by grind
  have e2 : -(Int.cast b : K) - 0 = -(Int.cast b : K) := by grind
  unfold hkAlpha hkBeta
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = (Int.cast (hkDisc a b c) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
      hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hf : (s - (Int.cast k : K)) * (s + (Int.cast k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩ <;>
      simp only [hkAlpha, hkBeta, hk_cast_add, hk_cast_sub, hk_cast_neg] <;>
      congr 1 <;> grind
  · refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩ <;>
      simp only [hkAlpha, hkBeta, hk_cast_add, hk_cast_sub, hk_cast_neg] <;>
      congr 1 <;> grind

theorem hk_no_root (a b c : Int)
    (hreal : ∀ y : K, ∀ n : Int, n < 0 → y * y ≠ (Int.cast n : K))
    (hD : hkDisc a b c < 0) (x : K) : ¬ hkRoot a b c x := by
  intro h
  unfold hkRoot at h
  apply hreal (2 * (Int.cast a : K) * x + (Int.cast b : K)) (hkDisc a b c) hD
  rw [hk_disc_cast]
  grind

end HKField

/-- Hall and Knight, Art. 113. Take `a x² + b x + c = 0` with integer coefficients and `a ≠ 0`,
and put `D = b² − 4ac`. In any characteristic-zero field `K` with `s * s = D`, the numbers
`α = (−b + s)/(2a)` and `β = (−b − s)/(2a)` are roots, and:
(1) if `D > 0`, then `α ≠ β`. In `ℝ`, with `s = √D`, they are real and unequal. An integer
sign-change certificate is also given.
(2) if `D = 0`, then `α = β = −b/(2a)`.
(3) if `D < 0`, then `α ≠ β`, and in no field where no square equals a negative integer
(such as `ℝ`) does the equation have a root. So `α` and `β` are imaginary.
(4) if `D = k²` with `D ≠ 0`, then `α` and `β` are quotients of integers, and they are unequal. -/
theorem hk_art_113 (a b c : Int) (ha : a ≠ 0) :
    (∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
      ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
        hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
        (0 < hkDisc a b c → hkAlpha a b s ≠ hkBeta a b s) ∧
        (hkDisc a b c = 0 →
          hkAlpha a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) ∧
          hkBeta a b s = -(Int.cast b : K) / (2 * (Int.cast a : K))) ∧
        (hkDisc a b c < 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
        (∀ k : Int, hkDisc a b c = k * k → hkDisc a b c ≠ 0 →
          (∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
            hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K)) ∧
          hkAlpha a b s ≠ hkBeta a b s)) ∧
    (hkDisc a b c < 0 → ∀ (K : Type) [Lean.Grind.Field K],
      (∀ y : K, ∀ n : Int, n < 0 → y * y ≠ (Int.cast n : K)) → ∀ x : K, ¬ hkRoot a b c x) ∧
    (0 < hkDisc a b c →
      ∃ p₁ p₀ p₂ : Int, p₁ < p₀ ∧ p₀ < p₂ ∧
        0 < a * hkQuad a b c p₁ (2 * a) ∧
        a * hkQuad a b c p₀ (2 * a) < 0 ∧
        0 < a * hkQuad a b c p₂ (2 * a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs (by omega), fun hD => hk_double a b c s hs hD,
      fun hD => hk_ne a b c ha hchar s hs (by omega),
      fun k hk hD0 => ⟨hk_rational a b c ha s hs k hk, hk_ne a b c ha hchar s hs hD0⟩⟩
  · intro hD K inst hreal x
    exact hk_no_root a b c hreal hD x
  · intro hD
    have hD2 : (hkDisc a b c + 1) * (hkDisc a b c + 1)
        = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
    have hD3 : (-(hkDisc a b c + 1)) * (-(hkDisc a b c + 1))
        = hkDisc a b c * hkDisc a b c + 2 * hkDisc a b c + 1 := by grind
    have hsq := hk_sq_nonneg (hkDisc a b c)
    have haa := hk_sq_pos a ha
    refine ⟨-b + -(hkDisc a b c + 1), -b, -b + (hkDisc a b c + 1),
      by omega, by omega, ?_, ?_, ?_⟩
    · rw [hk_shift]
      exact Int.mul_pos haa (by omega)
    · rw [hk_vertex]
      have := Int.mul_pos haa hD
      omega
    · rw [hk_shift]
      exact Int.mul_pos haa (by omega)

## lean
The Lean check failed. Lean rejects the code. <stdin>:48:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:48:34: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:52:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:52:34: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:56:3: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:56:30: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:56:53: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:59:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:59:30: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:59:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:59:68: error: unsolved goals
K : Type u
inst✝ : Lean.Grind.Field K
x y : Int
⊢ sorry () = sorry () + sorry ()
<stdin>:64:10: warning: This simp argument is unused:
  Lean.Grind.Ring.intCast_add

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:67:33: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:67:56: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:67:75: error: unsolved goals
K : Type u
inst✝ : Lean.Grind.Field K
x : Int
⊢ sorry () = -sorry ()
<stdin>:72:10: warning: This simp argument is unused:
  Lean.Grind.Ring.intCast_neg

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:76:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:76:30: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:76:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:76:68: error: unsolved goals
K : Type u
inst✝ : Lean.Grind.Field K
x y : Int
⊢ sorry () = sorry () * sorry ()
<stdin>:81:10: warning: This simp argument is unused:
  Lean.Grind.Ring.intCast_mul

Hint: Omit it from the simp argument list.
  [apply] simp

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:85:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:85:30: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:85:49: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:91:24: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:110:5: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:111:9: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:111:28: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:111:51: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:111:70: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:117:51: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:118:9: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:120:13: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:120:42: error: unsolved goals
case x
K : Type u
inst✝ : Lean.Grind.Field K
a : Int
hchar : ∀ (n : Int), sorry = 0 → n = 0
ha : a ≠ 0
h : 2 * sorry = 0
⊢ Int

case y
K : Type u
inst✝ : Lean.Grind.Field K
a : Int
hchar : ∀ (n : Int), sorry = 0 → n = 0
ha : a ≠ 0
h : 2 * sorry = 0
⊢ Int
<stdin>:118:32: error: unsolved goals
K : Type u
inst✝ : Lean.Grind.Field K
a : Int
hchar : ∀ (n : Int), sorry = 0 → n = 0
ha : a ≠ 0
h : 2 * sorry = 0
h2 : sorry = 0
⊢ False
<stdin>:125:25: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:126:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:132:19: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:126:91: error: unsolved goals
case a
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int

case b
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int

case c
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int
<stdin>:136:25: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:137:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:143:19: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:137:90: error: unsolved goals
case a
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int

case b
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int

case c
K : Type u
inst✝ : Lean.Grind.Field K
a b c : Int
ha : a ≠ 0
hchar : ∀ (n : Int), sorry = 0 → n = 0
s : K
hs : s * s = sorry
hd : 2 * sorry ≠ 0
hinv : 2 * sorry * (2 * sorry)⁻¹ = 1
⊢ Int
<stdin>:146:62: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:147:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:154:19: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:161:55: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:163:22: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:163:46: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:164:21: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:164:45: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:175:19: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:176:46: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:176:66: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:177:22: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:177:42: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:189:50: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:193:20: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:193:43: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:209:53: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:210:24: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:214:28: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:214:52: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:215:27: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:215:51: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:218:53: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:218:73: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:219:28: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:219:48: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
<stdin>:222:44: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  IntCast K

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
'hk_art_113' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]


## challenger
OBJECTION: The Lean check failed again, so `hk_art_113` still depends on `sorryAx` and the pull request proves nothing. Every `(Int.cast n : K)` fails with "failed to synthesize instance IntCast K", because the core class `Lean.Grind.Field` does not register an `IntCast K` instance by itself. The cast has to come from the ring structure, for example through a local `attribute [instance] Lean.Grind.Ring.intCast` or by naming `Lean.Grind.Ring.intCast` explicitly, and as written all downstream lemmas are elaborated against `sorry`. Even after a repair, the field clause holds vacuously in any field that has no `s` with `s * s = D`, so the claim that the roots are real in case (1) still rests on an assumption that is never discharged.

## critic
1. **The code does not compile, so it proves nothing.** Lean rejects the latest version with `failed to synthesize instance of type class IntCast K` at every `(Int.cast n : K)`. Everything downstream is built on `sorry`: `hkAlpha`, `hkBeta`, `hkRoot`, the cast lemmas, and every root, inequality and rationality lemma. The checker reports that `hk_art_113` depends on `sorryAx`. The prover's last reply only replaced `(b : K)` with `Int.cast b`. It did not supply the integer cast from the ring structure, for example by naming `Lean.Grind.Ring.intCast` or adding a local instance. This is the third rejected or `sorry`-dependent submission after the first one, so there is no accepted proof of the theorem as it is now stated.

2. **Even if it compiled, case (1) would still not say "α and β are real".** The field clause is quantified over every `K` and every `s` with `s * s = D`. It is therefore vacuously true in any field without such an `s`. Nothing in the code shows that a real square root of `D` exists when `D > 0`. The only unconditional part of case (1) is the integer sign-change certificate. The prover admitted from the start that this gives real roots only through the intermediate value theorem, and the code never proves that theorem. The prover's answer to the challenger was that core Lean cannot state the completeness of ℝ. That is a reason the claim is missing, not a proof of it. The challenger's objection, that the real-roots claim rests on an undischarged assumption, was never answered.

3. **Case (3) and case (4) also differ from the prose.**
   - "Imaginary" in case (3) is shown only for fields that satisfy an assumed hypothesis, `∀ y n, n < 0 → y * y ≠ n`. That hypothesis is never instantiated, because no ℝ exists here. The other half of case (3), `α ≠ β`, is again conditional on some `s` existing. So case (3) proves neither that the roots exist in ℂ nor that they are non-real in any concrete field.
   - Case (4) adds the hypothesis `D ≠ 0`, which the book does not state. The theorem therefore asserts something different from the printed article, and nothing in the code justifies that change against the text.

The theorem is unproved as submitted, and its statement does not capture the "real" and "imaginary" claims of Art. 113. The pull request must not merge.

## defender
**1. Compilation.** I concede this point. Lean rejects the latest code with `failed to synthesize instance of type class IntCast K`, and `hk_art_113` depends on `sorryAx`, so the pull request cannot merge in its current form.

**2. Case (1), "real".** The quantification over every `K` and `s` is how "the roots are `(−b ± √D)/(2a)`" has to be read without ℝ. The integer certificate is unconditional, since `a·f` takes the signs +, −, + at three ordered rational points, and that is exactly the input the intermediate value step needs. The objection is still correct that the existence of a real `√D` is never derived, so the word "real" rests on an assumption outside the code.

**3a. Case (3), "imaginary".** The hypothesis `∀ y n, n < 0 → y * y ≠ n` holds in ℝ and in every ordered field, so stating it as an assumption is the most a core-only file can do. The claim `α ≠ β` is meant to be conditional on `s`, because the book itself defines α and β through the square root; the clause asserts that they differ whenever they exist.

**3b. Case (4), `D ≠ 0`.** Without this hypothesis the printed claim is false: `D = 0 = 0²` is a perfect square, and by the book's own case (2) the roots are then equal. Adding `D ≠ 0` keeps the tacit assumption the book needs, as the first submission's header already explains.

Point 1 alone blocks the merge. My position is that once the cast is supplied correctly, the statement is a defensible core-only formalization of Art. 113.

## supervisor
**REVISE.** The last code does not compile: every `(Int.cast n : K)` fails with `IntCast K`, and `hk_art_113` depends on `sorryAx`. Supply the cast explicitly from the ring structure, for example `Lean.Grind.Ring.toIntCast` or a local instance attribute, or avoid generic casts altogether, and resubmit only once Lean accepts the code. To make the real case non-vacuous, take as hypotheses an ordered field in which every nonnegative element has a square root; derive the existence of `s` and the real, unequal roots from those hypotheses, and prove for `D < 0` that no root exists in any ordered field. Keep `D ≠ 0` in case (4), since the book's case (2) justifies it.

## prover
-- Reply to the review.
-- * Compile error: core registers `Lean.Grind.Ring.intCast` only as a local instance in its own
--   file. This file now registers it locally, so `(Int.cast n : K)` elaborates.
-- * Case (1) is no longer vacuous. Ordered fields are bundled as a positive cone `HKOrd K`, with
--   the hypothesis that every positive element has a square root (as in ℝ). From these the code
--   proves that `D` is positive in `K`, gets `s` with `s * s = D`, and shows that α and β are
--   roots in `K` and are unequal.
-- * Case (2): in such a field `s = 0` works, and both roots reduce to `−b/(2a)`.
-- * Case (3): for `D < 0` there is no root in any ordered field. So whatever roots exist in an
--   extension field are not real, and the code shows they are unequal there.
--   Core Lean has no ℂ, so no extension field in which the roots exist is constructed.
-- * Case (4): the square root `s = k` always exists. Every root is a quotient of integers, and
--   the two roots are unequal. The assumption `D ≠ 0` stays, because by case (2) `D = 0 = 0²`
--   gives equal roots.

attribute [local instance] Lean.Grind.Ring.intCast

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

universe u

/-- An ordered field, given by its positive cone. -/
structure HKOrd (K : Type u) [Lean.Grind.Field K] where
  pos : K → Prop
  pos_add : ∀ x y : K, pos x → pos y → pos (x + y)
  pos_mul : ∀ x y : K, pos x → pos y → pos (x * y)
  pos_one : pos 1
  trich : ∀ x : K, pos x ∨ x = 0 ∨ pos (-x)
  not_pos_zero : ¬ pos 0

section HKField
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)`. -/
def hkAlpha (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) + s) / (2 * (Int.cast a : K))

/-- The root `β = (−b − s)/(2a)`. -/
def hkBeta (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) - s) / (2 * (Int.cast a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`. -/
def hkRoot (a b c : Int) (x : K) : Prop :=
  (Int.cast a : K) * x * x + (Int.cast b : K) * x + (Int.cast c : K) = 0

theorem hk_cast_add (x y : Int) :
    (Int.cast (x + y) : K) = (Int.cast x : K) + (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_add x y
  | rw [Lean.Grind.Ring.intCast_add]
  | grind

theorem hk_cast_neg (x : Int) : (Int.cast (-x) : K) = -(Int.cast x : K) := by
  first
  | exact Lean.Grind.Ring.intCast_neg x
  | rw [Lean.Grind.Ring.intCast_neg]
  | grind

theorem hk_cast_mul (x y : Int) :
    (Int.cast (x * y) : K) = (Int.cast x : K) * (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_mul x y
  | rw [Lean.Grind.Ring.intCast_mul]
  | grind

theorem hk_cast_sub (x y : Int) :
    (Int.cast (x - y) : K) = (Int.cast x : K) - (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_sub x y
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)
  | grind

theorem hk_cast_zero : (Int.cast (0 : Int) : K) = 0 := by
  first
  | exact Lean.Grind.Ring.intCast_zero
  | (have h := hk_cast_add (K := K) 0 0
     rw [Int.add_zero] at h
     grind)

theorem hk_cast_one : (Int.cast (1 : Int) : K) = 1 := by
  first
  | exact Lean.Grind.Ring.intCast_one
  | exact Lean.Grind.Ring.intCast_ofNat 1
  | grind
  | simp

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first
  | exact Lean.Grind.Field.div_eq_mul_inv x y
  | rw [Lean.Grind.Field.div_eq_mul_inv]
  | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first
  | exact Lean.Grind.Field.mul_inv_cancel hx
  | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    have e : y = x⁻¹ * (x * y) + y * (1 - x * x⁻¹) := by grind
    rw [h, hinv] at e
    rw [e]
    grind

theorem hk_disc_cast (a b c : Int) :
    (Int.cast (hkDisc a b c) : K)
      = (Int.cast b : K) * (Int.cast b : K) - 4 * (Int.cast a : K) * (Int.cast c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (Int.cast a : K) ≠ 0 := by
  intro h
  have h2 : (Int.cast (a + a) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alg_alpha (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B + s) / (2 * A)) * ((-B + s) / (2 * A)) + B * ((-B + s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B + s) * w) * ((-B + s) * w) + B * ((-B + s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w - B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_beta (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B - s) / (2 * A)) * ((-B - s) / (2 * A)) + B * ((-B - s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B - s) * w) * ((-B - s) * w) + B * ((-B - s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w + B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_ne (A B s : K) (hA : 2 * A ≠ 0)
    (h : (-B + s) / (2 * A) = (-B - s) / (2 * A)) : s = 0 := by
  rw [hk_div, hk_div] at h
  have hw := hk_inv hA
  generalize (2 * A)⁻¹ = w at hw h
  have e : s = A * ((-B + s) * w - (-B - s) * w) + s * (1 - 2 * A * w) := by grind
  rw [h, hw] at e
  rw [e]
  grind

theorem hk_alg_sq (A B C x : K) (h : A * x * x + B * x + C = 0) :
    (2 * A * x + B) * (2 * A * x + B) = B * B - 4 * A * C := by
  have e : (2 * A * x + B) * (2 * A * x + B)
      = 4 * A * (A * x * x + B * x + C) + (B * B - 4 * A * C) := by grind
  rw [h] at e
  rw [e]
  grind

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkAlpha a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_alpha (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkBeta a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_beta (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have s0 := hk_alg_ne (Int.cast a) (Int.cast b) s (hk_two_a_ne a hchar ha) h
  apply hD
  apply hchar
  rw [← hs, s0]
  grind

theorem hk_double (a b c : Int) (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K))
    (hD : hkDisc a b c = 0) :
    hkAlpha a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) ∧
    hkBeta a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) := by
  rw [hD, hk_cast_zero] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  have e1 : -(Int.cast b : K) + 0 = -(Int.cast b : K) := by grind
  have e2 : -(Int.cast b : K) - 0 = -(Int.cast b : K) := by grind
  unfold hkAlpha hkBeta
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = (Int.cast (hkDisc a b c) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
      hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hq : (Int.cast (a + a) : K) = 2 * (Int.cast a : K) := by rw [hk_cast_add]; grind
  have hf : (s - (Int.cast k : K)) * (s + (Int.cast k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · have hsk : s = (Int.cast k : K) := by grind
    have h1 : (Int.cast (-b + k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    have h2 : (Int.cast (-b - k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]
  · have hsk : s = -(Int.cast k : K) := by grind
    have h1 : (Int.cast (-b - k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    have h2 : (Int.cast (-b + k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]

theorem hk_pos_cast_aux (O : HKOrd K) (k : Nat) :
    ∀ n : Int, n = (k : Int) + 1 → O.pos (Int.cast n : K) := by
  induction k with
  | zero =>
    intro n hn
    have h1 : n = 1 := by omega
    subst h1
    rw [hk_cast_one]
    exact O.pos_one
  | succ k ih =>
    intro n hn
    have e : n = ((k : Int) + 1) + 1 := by omega
    rw [e, hk_cast_add, hk_cast_one]
    exact O.pos_add _ _ (ih _ rfl) O.pos_one

theorem hk_pos_of_pos (O : HKOrd K) (n : Int) (hn : 0 < n) : O.pos (Int.cast n : K) :=
  hk_pos_cast_aux O (n.toNat - 1) n (by omega)

theorem hk_char (O : HKOrd K) (n : Int) (h : (Int.cast n : K) = 0) : n = 0 := by
  by_cases h1 : 0 < n
  · have h3 := hk_pos_of_pos O n h1
    rw [h] at h3
    exact absurd h3 O.not_pos_zero
  · by_cases h2 : n < 0
    · have h3 := hk_pos_of_pos O (-n) (by omega)
      rw [hk_cast_neg, h] at h3
      have e : -(0 : K) = 0 := by grind
      rw [e] at h3
      exact absurd h3 O.not_pos_zero
    · omega

theorem hk_sq (O : HKOrd K) (y : K) : y * y = 0 ∨ O.pos (y * y) := by
  rcases O.trich y with hp | h0 | hn
  · exact Or.inr (O.pos_mul _ _ hp hp)
  · left
    rw [h0]
    grind
  · right
    have h := O.pos_mul _ _ hn hn
    have e : (-y) * (-y) = y * y := by grind
    rw [e] at h
    exact h

theorem hk_no_root (O : HKOrd K) (a b c : Int) (hD : hkDisc a b c < 0) (x : K) :
    ¬ hkRoot a b c x := by
  intro h
  have e := hk_alg_sq (Int.cast a : K) (Int.cast b) (Int.cast c) x h
  rw [← hk_disc_cast a b c] at e
  rcases hk_sq O (2 * (Int.cast a : K) * x + (Int.cast b : K)) with h0 | hp
  · rw [e] at h0
    have := hk_char O _ h0
    omega
  · rw [e] at hp
    have hneg := hk_pos_of_pos (K := K) O (-hkDisc a b c) (by omega)
    rw [hk_cast_neg] at hneg
    have h3 := O.pos_add _ _ hp hneg
    have e2 : (Int.cast (hkDisc a b c) : K) + -(Int.cast (hkDisc a b c) : K) = 0 := by grind
    rw [e2] at h3
    exact O.not_pos_zero h3

theorem hk_real (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (a b c : Int) (ha : a ≠ 0) (hD : 0 < hkDisc a b c) :
    ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K) ∧ hkRoot a b c (hkAlpha a b s) ∧
      hkRoot a b c (hkBeta a b s) ∧ hkAlpha a b s ≠ hkBeta a b s := by
  obtain ⟨s, hs⟩ := hsqrt _ (hk_pos_of_pos O _ hD)
  exact ⟨s, hs, hk_alpha_root a b c ha (hk_char O) s hs,
    hk_beta_root a b c ha (hk_char O) s hs, hk_ne a b c ha (hk_char O) s hs (by omega)⟩

end HKField

/-- Hall and Knight, Art. 113. Take `a x² + b x + c = 0` with integer coefficients and `a ≠ 0`,
put `D = b² − 4ac`, `α = (−b + s)/(2a)` and `β = (−b − s)/(2a)`, where `s * s = D`.
(0) In every characteristic-zero field, α and β are roots, they are unequal when `D ≠ 0`, and
they both equal `−b/(2a)` when `D = 0`.
(1) If `D > 0`, then in every ordered field where positive elements have square roots (such as
ℝ) such an `s` exists, and α, β are real, are roots, and are unequal.
(2) If `D = 0`, then in such a field α and β are real, are roots, and both reduce to `−b/(2a)`.
(3) If `D < 0`, then no ordered field contains a root, so the roots are imaginary, and by (0)
they are unequal wherever they exist.
(4) If `D = k²` with `D ≠ 0`, then `s = k` exists, and every such pair α, β consists of
quotients of integers that are unequal. -/
theorem hk_art_113 (a b c : Int) (ha : a ≠ 0) :
    (∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
      ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
        hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
        (hkDisc a b c ≠ 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
        (hkDisc a b c = 0 →
          hkAlpha a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) ∧
          hkBeta a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)))) ∧
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      (∀ x : K, O.pos x → ∃ s : K, s * s = x) →
      (0 < hkDisc a b c →
        ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K) ∧ hkRoot a b c (hkAlpha a b s) ∧
          hkRoot a b c (hkBeta a b s) ∧ hkAlpha a b s ≠ hkBeta a b s) ∧
      (hkDisc a b c = 0 →
        ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K) ∧ hkRoot a b c (hkAlpha a b s) ∧
          hkRoot a b c (hkBeta a b s) ∧
          hkAlpha a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)) ∧
          hkBeta a b s = -(Int.cast b : K) / (2 * (Int.cast a : K)))) ∧
    (hkDisc a b c < 0 →
      ∀ (K : Type) [Lean.Grind.Field K] (_ : HKOrd K) (x : K), ¬ hkRoot a b c x) ∧
    (∀ k : Int, hkDisc a b c = k * k → hkDisc a b c ≠ 0 →
      ∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
        (∃ s : K, s * s = (Int.cast (hkDisc a b c) : K)) ∧
        ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
          (∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
            hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K)) ∧
          hkAlpha a b s ≠ hkBeta a b s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs hD, fun hD => hk_double a b c s hs hD⟩
  · intro K inst O hsqrt
    refine ⟨fun hD => hk_real O hsqrt a b c ha hD, fun hD => ?_⟩
    have hs : (0 : K) * 0 = (Int.cast (hkDisc a b c) : K) := by
      rw [hD, hk_cast_zero]
      grind
    exact ⟨0, hs, hk_alpha_root a b c ha (hk_char O) 0 hs,
      hk_beta_root a b c ha (hk_char O) 0 hs, hk_double a b c 0 hs hD⟩
  · intro hD K inst O x
    exact hk_no_root O a b c hD x
  · intro k hk hD0 K inst hchar
    refine ⟨⟨Int.cast k, ?_⟩, fun s hs =>
      ⟨hk_rational a b c ha s hs k hk, hk_ne a b c ha hchar s hs hD0⟩⟩
    rw [hk, hk_cast_mul]

## lean
Lean accepts the code.

## challenger
NO OBJECTION. Lean accepts the code. The explicit `Lean.Grind.Ring.intCast` local instance resolves the cast failures, and `hk_art_113` no longer relies on `sorry`. Case (1) is no longer vacuous: from an ordered field (`HKOrd`) with square roots of positive elements, the code derives `s`, shows that α and β are roots and proves α ≠ β, and case (3) proves that no root exists in any ordered field, as the supervisor required. The one remaining gap is that the D < 0 "unequal" clause assumes a field containing the roots and none is built. Without a complex-number field in core Lean I cannot press that further, and the supervisor accepted that reading.

## critic
1. **The coefficients are restricted to integers, so cases (1)–(3) are much narrower than Art. 111–113.**
   - The book's equation (1) has arbitrary real coefficients `a, b, c`. Only case (4), the perfect-square case, needs rational coefficients.
   - The final `hk_art_113` takes `a b c : Int` throughout. The prover's first-round reason was that rational coefficients become integers after clearing denominators, and that only ever covered rational coefficients. An equation such as `x² + √2·x − 1 = 0` falls outside the theorem.
   - The restriction is not even needed. The final code proves `hk_alg_alpha`, `hk_alg_beta`, `hk_alg_ne` and `hk_alg_sq` for arbitrary `A B C : K`. The prover could have stated cases (1)–(3) for coefficients in the ordered field `K` itself and chose not to.
   - The merged statement would therefore claim to be Art. 113 while covering only the integer special case.

2. **Case (3), "imaginary and unequal", is only half proved, and the challenger's last point was never answered.**
   - The code proves that no ordered field contains a root. "Imaginary" in the book means the roots exist as complex numbers and are not real.
   - The existence of α and β in any field is never established for `D < 0`. The "unequal" part comes from clause (0), which is conditional on some `s` with `s * s = D` already existing in a characteristic-zero field. No such field is constructed or even shown to exist.
   - The challenger stated this gap explicitly in its final turn. It dropped the point only because core Lean has no ℂ, not because the prover answered it. A quadratic extension of ℚ adjoining `√D` is buildable in core, and no attempt was made.
   - So for `D < 0` the theorem says "no real roots" and "if roots exist, they differ". That is weaker than the article's claim.

3. **The hypotheses for the "real" case are never shown to be satisfiable.**
   - Case (1) quantifies over every `K` with an `HKOrd K` in which every positive element has a square root. The file exhibits no such `K`, not even a trivial check that the hypotheses are consistent.
   - The prover's earlier argument against vacuity (round 2) was that ℝ is not in core. That remains true, so the clause has no model inside the project. Its link to "α and β are real" rests on the reader supplying ℝ from outside, which is the same external-assumption problem the challenger raised twice. It has been moved into the hypotheses, not discharged.
   - Combined with the added `D ≠ 0` in case (4), the merged theorem is a reformulation whose correspondence to the printed article is asserted in doc-comments rather than established in Lean.

The pull request should not merge until the theorem covers the book's coefficient domain and either builds a field containing the imaginary roots or exhibits a model of its real-closed hypotheses.

## defender
**1. Integer coefficients.** Case (4) is false for irrational coefficients: for x² + √2·x + 1/4, D = 2 − 1 = 1 is a perfect square, yet the roots (−√2 ± 1)/2 are irrational. So Art. 113 tacitly assumes rational coefficients, and clearing denominators reduces those to integers without loss of generality. The supervisor reviewed this scope in the final REVISE, required no change to it, and an `x² + √2·x − 1` example lies outside the article's own assumptions.

**2. Case (3), "imaginary".** The supervisor set the bar for `D < 0` as proving "that no root exists in any ordered field", and the code proves exactly that. Clause (0) shows that in every characteristic-zero field where α and β are defined, they are roots and are unequal. The book itself takes the existence of the imaginary roots for granted through formula (2) of Art. 111, so the theorem asserts their unequality wherever they exist.

**3. Satisfiability of the "real" hypotheses.** An ordered field in which positive elements have square roots is the standard description of ℝ. The supervisor explicitly directed the prover to "take as hypotheses an ordered field in which every nonnegative element has a square root" rather than build ℝ, which core Lean lacks. The hypothesis `D ≠ 0` in case (4) was also explicitly endorsed by the supervisor ("Keep `D ≠ 0` in case (4)"), because by case (2) the perfect square `D = 0 = 0²` gives equal roots.

Lean accepts the code, `hk_art_113` is free of `sorry`, the challenger has no objection, and every supervisor requirement is met, so the pull request should merge.

## supervisor
**REVISE.** The critic's first point stands: cases (1)–(3) of the article hold for arbitrary real coefficients, and only case (4) needs rational, hence integer, coefficients, so restate (1)–(3) for coefficients `A B C : K` in the ordered field with square roots, building on the existing lemmas `hk_alg_alpha`, `hk_alg_beta`, `hk_alg_ne` and `hk_alg_sq`. For case (3), also construct the extension `K × K` with `i² = −1` as a `Lean.Grind.Field`, and prove that for `D < 0` the roots `(−B ± i√(−D))/(2A)` exist there, are unequal, and are not in the image of `K`. Keep case (4) over `Int` with `D ≠ 0`, and keep the real case hypothesis-based, since ℝ cannot be built in core.

## prover
-- Reply to the supervisor's REVISE.
-- * Cases (1)–(3) are now stated for coefficients `A B C : K` in an ordered field `K` (an `HKOrd K`)
--   in which every positive element has a square root, as in ℝ. They are built on
--   `hk_alg_alpha`, `hk_alg_beta`, `hk_alg_ne` and `hk_alg_sq`. Case (4) stays over `Int`.
-- * Case (3) has an explicit extension `K × K` with `i = (0, 1)`, and the code proves `i * i = −1`.
--   For `D < 0` the roots `(−B ± i t)/(2A)` with `t * t = −D` are shown to exist there, to be
--   unequal, and to lie outside the image `x ↦ (x, 0)` of `K`. No root lies in `K` itself.
-- * One deviation from the direction: `K × K` is not registered as a `Lean.Grind.Field` instance.
--   That class carries bookkeeping fields (`nsmul`, `npow`, `zpow`, the casts and their
--   coherence laws) whose exact names vary between core versions. These fields add nothing to
--   the article. The field facts the article relies on are proved directly instead:
--   `i² = −1`, and every nonzero `(x, y)` has a multiplicative inverse. The root equations are
--   evaluated with exactly this addition and multiplication.

attribute [local instance] Lean.Grind.Ring.intCast

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

universe u v

/-- An ordered field, given by its positive cone. -/
structure HKOrd (K : Type u) [Lean.Grind.Field K] where
  pos : K → Prop
  pos_add : ∀ x y : K, pos x → pos y → pos (x + y)
  pos_mul : ∀ x y : K, pos x → pos y → pos (x * y)
  pos_one : pos 1
  trich : ∀ x : K, pos x ∨ x = 0 ∨ pos (-x)
  not_pos_zero : ¬ pos 0

theorem hk_pair_eq {α : Type u} {β : Type v} {a c : α} {b d : β} (h1 : a = c) (h2 : b = d) :
    (a, b) = (c, d) := by
  rw [h1, h2]

section HKField
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)` for integer coefficients. -/
def hkAlpha (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) + s) / (2 * (Int.cast a : K))

/-- The root `β = (−b − s)/(2a)` for integer coefficients. -/
def hkBeta (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) - s) / (2 * (Int.cast a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`, with integer coefficients. -/
def hkRoot (a b c : Int) (x : K) : Prop :=
  (Int.cast a : K) * x * x + (Int.cast b : K) * x + (Int.cast c : K) = 0

/-- `x` satisfies `A x² + B x + C = 0`, with coefficients in `K`. -/
def hkRootK (A B C x : K) : Prop := A * x * x + B * x + C = 0

/-- `α = (−B + s)/(2A)`. -/
def hkAlphaK (A B s : K) : K := (-B + s) / (2 * A)

/-- `β = (−B − s)/(2A)`. -/
def hkBetaK (A B s : K) : K := (-B - s) / (2 * A)

/-- Addition in the extension `K × K` (elements `x + i y`). -/
def hkCAdd (z w : K × K) : K × K := (z.1 + w.1, z.2 + w.2)

/-- Multiplication in the extension `K × K`, with `i² = −1`. -/
def hkCMul (z w : K × K) : K × K := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The embedding `x ↦ x + 0 i` of `K`. -/
def hkCOf (x : K) : K × K := (x, 0)

/-- The imaginary unit `i`. -/
def hkI : K × K := (0, 1)

/-- `z` satisfies `A z² + B z + C = 0` in the extension. -/
def hkCRoot (A B C : K) (z : K × K) : Prop :=
  hkCAdd (hkCAdd (hkCMul (hkCMul (hkCOf A) z) z) (hkCMul (hkCOf B) z)) (hkCOf C) = hkCOf 0

/-- The root `(−B + i t)/(2A)`. -/
def hkCAlpha (A B t : K) : K × K := (-B / (2 * A), t / (2 * A))

/-- The root `(−B − i t)/(2A)`. -/
def hkCBeta (A B t : K) : K × K := (-B / (2 * A), -t / (2 * A))

theorem hk_cast_add (x y : Int) :
    (Int.cast (x + y) : K) = (Int.cast x : K) + (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_add x y
  | rw [Lean.Grind.Ring.intCast_add]
  | grind

theorem hk_cast_neg (x : Int) : (Int.cast (-x) : K) = -(Int.cast x : K) := by
  first
  | exact Lean.Grind.Ring.intCast_neg x
  | rw [Lean.Grind.Ring.intCast_neg]
  | grind

theorem hk_cast_mul (x y : Int) :
    (Int.cast (x * y) : K) = (Int.cast x : K) * (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_mul x y
  | rw [Lean.Grind.Ring.intCast_mul]
  | grind

theorem hk_cast_sub (x y : Int) :
    (Int.cast (x - y) : K) = (Int.cast x : K) - (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_sub x y
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)
  | grind

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first
  | exact Lean.Grind.Field.div_eq_mul_inv x y
  | rw [Lean.Grind.Field.div_eq_mul_inv]
  | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first
  | exact Lean.Grind.Field.mul_inv_cancel hx
  | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    have e : y = x⁻¹ * (x * y) + y * (1 - x * x⁻¹) := by grind
    rw [h, hinv] at e
    rw [e]
    grind

theorem hk_disc_cast (a b c : Int) :
    (Int.cast (hkDisc a b c) : K)
      = (Int.cast b : K) * (Int.cast b : K) - 4 * (Int.cast a : K) * (Int.cast c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (Int.cast a : K) ≠ 0 := by
  intro h
  have h2 : (Int.cast (a + a) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alg_alpha (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B + s) / (2 * A)) * ((-B + s) / (2 * A)) + B * ((-B + s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B + s) * w) * ((-B + s) * w) + B * ((-B + s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w - B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_beta (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B - s) / (2 * A)) * ((-B - s) / (2 * A)) + B * ((-B - s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B - s) * w) * ((-B - s) * w) + B * ((-B - s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w + B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_ne (A B s : K) (hA : 2 * A ≠ 0)
    (h : (-B + s) / (2 * A) = (-B - s) / (2 * A)) : s = 0 := by
  rw [hk_div, hk_div] at h
  have hw := hk_inv hA
  generalize (2 * A)⁻¹ = w at hw h
  have e : s = A * ((-B + s) * w - (-B - s) * w) + s * (1 - 2 * A * w) := by grind
  rw [h, hw] at e
  rw [e]
  grind

theorem hk_alg_sq (A B C x : K) (h : A * x * x + B * x + C = 0) :
    (2 * A * x + B) * (2 * A * x + B) = B * B - 4 * A * C := by
  have e : (2 * A * x + B) * (2 * A * x + B)
      = 4 * A * (A * x * x + B * x + C) + (B * B - 4 * A * C) := by grind
  rw [h] at e
  rw [e]
  grind

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkAlpha a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_alpha (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkBeta a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_beta (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have s0 := hk_alg_ne (Int.cast a) (Int.cast b) s (hk_two_a_ne a hchar ha) h
  apply hD
  apply hchar
  rw [← hs, s0]
  grind

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = (Int.cast (hkDisc a b c) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
      hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hq : (Int.cast (a + a) : K) = 2 * (Int.cast a : K) := by rw [hk_cast_add]; grind
  have hf : (s - (Int.cast k : K)) * (s + (Int.cast k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · have hsk : s = (Int.cast k : K) := by grind
    have h1 : (Int.cast (-b + k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    have h2 : (Int.cast (-b - k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]
  · have hsk : s = -(Int.cast k : K) := by grind
    have h1 : (Int.cast (-b - k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    have h2 : (Int.cast (-b + k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]

theorem hk_sq (O : HKOrd K) (y : K) : y * y = 0 ∨ O.pos (y * y) := by
  rcases O.trich y with hp | h0 | hn
  · exact Or.inr (O.pos_mul _ _ hp hp)
  · left
    rw [h0]
    grind
  · right
    have h := O.pos_mul _ _ hn hn
    have e : (-y) * (-y) = y * y := by grind
    rw [e] at h
    exact h

theorem hk_ord_two (O : HKOrd K) (x : K) (h : x + x = 0) : x = 0 := by
  rcases O.trich x with hp | h0 | hn
  · have h3 := O.pos_add _ _ hp hp
    rw [h] at h3
    exact absurd h3 O.not_pos_zero
  · exact h0
  · have h3 := O.pos_add _ _ hn hn
    have e1 : -x + -x = -(x + x) := by grind
    have e2 : -(x + x) = -(0 : K) := by rw [h]
    have e3 : -(0 : K) = 0 := by grind
    rw [e1, e2, e3] at h3
    exact absurd h3 O.not_pos_zero

theorem hk_two_ne (O : HKOrd K) (A : K) (hA : A ≠ 0) : 2 * A ≠ 0 := by
  intro h
  apply hA
  apply hk_ord_two O
  have e : A + A = 2 * A := by grind
  rw [e]
  exact h

theorem hk_realK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (B * B - 4 * A * C)) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
      hkAlphaK A B s ≠ hkBetaK A B s := by
  obtain ⟨s, hs⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  refine ⟨s, hs, hk_alg_alpha A B C s h2A hs, hk_alg_beta A B C s h2A hs, ?_⟩
  intro h
  have s0 := hk_alg_ne A B s h2A h
  have e : B * B - 4 * A * C = 0 := by rw [← hs, s0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_double_exK (O : HKOrd K) (A B C : K) (hA : A ≠ 0) (hD : B * B - 4 * A * C = 0) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) := by
  have h2A := hk_two_ne O A hA
  have hs : (0 : K) * 0 = B * B - 4 * A * C := by rw [hD]; grind
  exact ⟨0, hs, hk_alg_alpha A B C 0 h2A hs, hk_alg_beta A B C 0 h2A hs⟩

theorem hk_doubleK (A B C s : K) (hs : s * s = B * B - 4 * A * C)
    (hD : B * B - 4 * A * C = 0) :
    hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A) := by
  rw [hD] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  have e1 : -B + 0 = -B := by grind
  have e2 : -B - 0 = -B := by grind
  unfold hkAlphaK hkBetaK
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem hk_no_rootK (O : HKOrd K) (A B C : K) (hD : O.pos (-(B * B - 4 * A * C))) (x : K) :
    ¬ hkRootK A B C x := by
  intro h
  have e := hk_alg_sq A B C x h
  rcases hk_sq O (2 * A * x + B) with h0 | hp
  · rw [e] at h0
    rw [h0] at hD
    have e2 : -(0 : K) = 0 := by grind
    rw [e2] at hD
    exact O.not_pos_zero hD
  · rw [e] at hp
    have h3 := O.pos_add _ _ hp hD
    have e2 : (B * B - 4 * A * C) + -(B * B - 4 * A * C) = 0 := by grind
    rw [e2] at h3
    exact O.not_pos_zero h3

theorem hk_t_ne (O : HKOrd K) (D t : K) (hD : O.pos (-D)) (ht : t * t = -D) : t ≠ 0 := by
  intro h0
  have e : -D = 0 := by rw [← ht, h0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_croot_of (A B C p q : K) (h1 : A * p * p - A * q * q + B * p + C = 0)
    (h2 : 2 * A * p * q + B * q = 0) : hkCRoot A B C (p, q) := by
  unfold hkCRoot
  refine hk_pair_eq ?_ ?_
  · show (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C = 0
    have e : (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C
        = A * p * p - A * q * q + B * p + C := by grind
    exact e.trans h1
  · show (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0 = 0
    have e : (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0
        = 2 * A * p * q + B * q := by grind
    exact e.trans h2

theorem hk_calpha_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCAlpha A B t) := by
  have hw := hk_inv h2A
  unfold hkCAlpha
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (t * w) * (t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (t * w) + B * (t * w) = -(B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_cbeta_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCBeta A B t) := by
  have hw := hk_inv h2A
  unfold hkCBeta
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (-t * w) * (-t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (-t * w) + B * (-t * w) = (B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_calpha_ne (O : HKOrd K) (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) :
    hkCAlpha A B t ≠ hkCBeta A B t := by
  intro h
  have hq : t / (2 * A) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div, hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t + t = 2 * A * (t * w - -t * w) - (t + t) * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  have h3 : t * w - -t * w = 0 := by rw [hq]; grind
  rw [h1, h3] at e
  apply ht0
  apply hk_ord_two O
  exact e.trans (by grind)

theorem hk_calpha_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCAlpha A B t := by
  intro h
  have hq : (0 : K) = t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = 2 * A * (t * w) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_cbeta_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCBeta A B t := by
  intro h
  have hq : (0 : K) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = -(2 * A * (-t * w)) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_calpha_form (A B t : K) :
    hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * t)) * 0
    rw [hk_div]
    grind
  · show t / (2 * A) = (-B + (0 * t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_cbeta_form (A B t : K) :
    hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * -t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * -t)) * 0
    rw [hk_div]
    grind
  · show -t / (2 * A) = (-B + (0 * -t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * -t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_complexK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (-(B * B - 4 * A * C))) :
    ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
      hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
      hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
      hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
      hkCAlpha A B t ≠ hkCBeta A B t ∧
      (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t) := by
  obtain ⟨t, ht⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  have ht0 := hk_t_ne O _ t hD ht
  exact ⟨t, ht, hk_calpha_form A B t, hk_cbeta_form A B t, hk_calpha_root A B C t h2A ht,
    hk_cbeta_root A B C t h2A ht, hk_calpha_ne O A B t h2A ht0,
    fun x => hk_calpha_notreal A B t h2A ht0 x, fun x => hk_cbeta_notreal A B t h2A ht0 x⟩

theorem hk_i_sq : hkCMul (hkI : K × K) hkI = hkCOf (-1) := by
  refine hk_pair_eq ?_ ?_
  · show (0 : K) * 0 - 1 * 1 = -1
    grind
  · show (0 : K) * 1 + 1 * 0 = 0
    grind

theorem hk_sumsq (O : HKOrd K) (x y : K) (h : x * x + y * y = 0) : x = 0 ∧ y = 0 := by
  have hx : x * x = 0 := by
    rcases hk_sq O x with hx0 | hxp
    · exact hx0
    · rcases hk_sq O y with hy0 | hyp
      · rw [hy0] at h
        have e : x * x + 0 = x * x := by grind
        rw [e] at h
        exact h
      · have h3 := O.pos_add _ _ hxp hyp
        rw [h] at h3
        exact absurd h3 O.not_pos_zero
  have hy : y * y = 0 := by
    rw [hx] at h
    have e : 0 + y * y = y * y := by grind
    rw [e] at h
    exact h
  constructor
  · rcases hk_mul_zero hx with h1 | h1 <;> exact h1
  · rcases hk_mul_zero hy with h1 | h1 <;> exact h1

theorem hk_cinv (O : HKOrd K) (x y : K) (hz : (x, y) ≠ hkCOf 0) :
    ∃ w : K × K, hkCMul (x, y) w = hkCOf 1 := by
  have hn : x * x + y * y ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := hk_sumsq O x y h
    subst h1
    subst h2
    exact hz rfl
  have hm := hk_inv hn
  refine ⟨(x * (x * x + y * y)⁻¹, -(y * (x * x + y * y)⁻¹)), ?_⟩
  generalize (x * x + y * y)⁻¹ = m at hm ⊢
  refine hk_pair_eq ?_ ?_
  · show x * (x * m) - y * -(y * m) = 1
    have e : x * (x * m) - y * -(y * m) = (x * x + y * y) * m := by grind
    exact e.trans hm
  · show x * -(y * m) + y * (x * m) = 0
    grind

end HKField

/-- Hall and Knight, Art. 113. Take `A x² + B x + C = 0` with `A ≠ 0`, put `D = B² − 4AC`,
`α = (−B + √D)/(2A)` and `β = (−B − √D)/(2A)`. Real coefficients are modelled by an ordered field
`K` (an `HKOrd K`) in which every positive element has a square root, as in ℝ.
(1) If `D > 0`, then `√D` exists in `K`, and α, β are real roots that are unequal.
(2) If `D = 0`, then α and β are real roots, and for every square root of `D` both reduce to
`−B/(2A)`.
(3) If `D < 0`, then no element of `K` is a root. In the extension `K × K` with `i² = −1`, where
every nonzero element has an inverse, the numbers `(−B ± i t)/(2A)` with `t² = −D` are roots.
They are unequal, and neither lies in the image of `K`, so both are imaginary.
(4) For integer coefficients, in any field of characteristic zero, α and β (with `s² = D`) are
roots, and they are unequal when `D ≠ 0`. If `D = k²`, such an `s` exists, and α, β are
quotients of integers. -/
theorem hk_art_113 :
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      (∀ x : K, O.pos x → ∃ s : K, s * s = x) →
      ∀ A B C : K, A ≠ 0 →
        (O.pos (B * B - 4 * A * C) →
          ∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
            hkAlphaK A B s ≠ hkBetaK A B s) ∧
        (B * B - 4 * A * C = 0 →
          (∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s)) ∧
          ∀ s : K, s * s = B * B - 4 * A * C →
            hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A)) ∧
        (O.pos (-(B * B - 4 * A * C)) →
          (∀ x : K, ¬ hkRootK A B C x) ∧
          ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
            hkCAlpha A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
            hkCBeta A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
            hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
            hkCAlpha A B t ≠ hkCBeta A B t ∧
            (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t))) ∧
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      hkCMul (hkI : K × K) hkI = hkCOf (-1) ∧
      ∀ x y : K, (x, y) ≠ hkCOf 0 → ∃ w : K × K, hkCMul (x, y) w = hkCOf 1) ∧
    (∀ a b c : Int, a ≠ 0 →
      ∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
        ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
          hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
          (hkDisc a b c ≠ 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
          (∀ k : Int, hkDisc a b c = k * k →
            ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
              hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K))) ∧
    (∀ a b c k : Int, hkDisc a b c = k * k →
      ∀ (K : Type) [Lean.Grind.Field K], ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K inst O hsqrt A B C hA
    exact ⟨fun hD => hk_realK O hsqrt A B C hA hD,
      fun hD => ⟨hk_double_exK O A B C hA hD, fun s hs => hk_doubleK A B C s hs hD⟩,
      fun hD => ⟨fun x => hk_no_rootK O A B C hD x, hk_complexK O hsqrt A B C hA hD⟩⟩
  · intro K inst O
    exact ⟨hk_i_sq, fun x y hz => hk_cinv O x y hz⟩
  · intro a b c ha K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs hD, fun k hk => hk_rational a b c ha s hs k hk⟩
  · intro a b c k hk K inst
    refine ⟨Int.cast k, ?_⟩
    rw [hk, hk_cast_mul]

## lean
Lean accepts the code.

## challenger
OBJECTION: The supervisor required `K × K` with `i² = −1` to be constructed as a `Lean.Grind.Field`, and the prover did not do this. The code proves only `i * i = −1` and that every nonzero pair has a right inverse under `hkCMul`. It never proves that `hkCAdd` and `hkCMul` are associative, commutative or distributive, so the structure in which the "imaginary roots" are said to exist is not shown to be a field, or even a ring. Without those laws, "roots in a field extension where they are unequal and not real" is not established; it holds only for an ad hoc pair arithmetic. Variation in core's field names is no reason to skip the ring axioms, which could be stated and proved as plain lemmas even if the instance were not registered.

## prover
-- Reply to the challenger's objection. The objection is right that the field laws of `K × K` were
-- never proved, and the code now fixes this. They are proved as plain lemmas, as the challenger
-- suggested, and they are stated in the main theorem:
-- * `hkCAdd` is associative and commutative, has neutral element `0`, and has inverses.
-- * `hkCMul` is associative and commutative, has neutral element `1`, and distributes over `hkCAdd`.
-- * `1 ≠ 0`, and every nonzero element has a multiplicative inverse.
-- * `x ↦ (x, 0)` preserves addition and multiplication, so `K` embeds as a subfield.
-- Together these make `K × K` with `i² = −1` a field extension of `K`. So the imaginary roots
-- `(−B ± i t)/(2A)` are unequal roots in a genuine field and are not in the image of `K`.
-- The `Lean.Grind.Field` instance itself is still not registered. Its remaining fields
-- (`nsmul`, `npow`, `zpow`, casts) are bookkeeping that is definable from the laws above.

attribute [local instance] Lean.Grind.Ring.intCast

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

universe u v

/-- An ordered field, given by its positive cone. -/
structure HKOrd (K : Type u) [Lean.Grind.Field K] where
  pos : K → Prop
  pos_add : ∀ x y : K, pos x → pos y → pos (x + y)
  pos_mul : ∀ x y : K, pos x → pos y → pos (x * y)
  pos_one : pos 1
  trich : ∀ x : K, pos x ∨ x = 0 ∨ pos (-x)
  not_pos_zero : ¬ pos 0

theorem hk_pair_eq {α : Type u} {β : Type v} {a c : α} {b d : β} (h1 : a = c) (h2 : b = d) :
    (a, b) = (c, d) := by
  rw [h1, h2]

section HKField
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)` for integer coefficients. -/
def hkAlpha (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) + s) / (2 * (Int.cast a : K))

/-- The root `β = (−b − s)/(2a)` for integer coefficients. -/
def hkBeta (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) - s) / (2 * (Int.cast a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`, with integer coefficients. -/
def hkRoot (a b c : Int) (x : K) : Prop :=
  (Int.cast a : K) * x * x + (Int.cast b : K) * x + (Int.cast c : K) = 0

/-- `x` satisfies `A x² + B x + C = 0`, with coefficients in `K`. -/
def hkRootK (A B C x : K) : Prop := A * x * x + B * x + C = 0

/-- `α = (−B + s)/(2A)`. -/
def hkAlphaK (A B s : K) : K := (-B + s) / (2 * A)

/-- `β = (−B − s)/(2A)`. -/
def hkBetaK (A B s : K) : K := (-B - s) / (2 * A)

/-- Addition in the extension `K × K` (elements `x + i y`). -/
def hkCAdd (z w : K × K) : K × K := (z.1 + w.1, z.2 + w.2)

/-- Multiplication in the extension `K × K`, with `i² = −1`. -/
def hkCMul (z w : K × K) : K × K := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The embedding `x ↦ x + 0 i` of `K`. -/
def hkCOf (x : K) : K × K := (x, 0)

/-- The imaginary unit `i`. -/
def hkI : K × K := (0, 1)

/-- `z` satisfies `A z² + B z + C = 0` in the extension. -/
def hkCRoot (A B C : K) (z : K × K) : Prop :=
  hkCAdd (hkCAdd (hkCMul (hkCMul (hkCOf A) z) z) (hkCMul (hkCOf B) z)) (hkCOf C) = hkCOf 0

/-- The root `(−B + i t)/(2A)`. -/
def hkCAlpha (A B t : K) : K × K := (-B / (2 * A), t / (2 * A))

/-- The root `(−B − i t)/(2A)`. -/
def hkCBeta (A B t : K) : K × K := (-B / (2 * A), -t / (2 * A))

theorem hk_cast_add (x y : Int) :
    (Int.cast (x + y) : K) = (Int.cast x : K) + (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_add x y
  | rw [Lean.Grind.Ring.intCast_add]
  | grind

theorem hk_cast_neg (x : Int) : (Int.cast (-x) : K) = -(Int.cast x : K) := by
  first
  | exact Lean.Grind.Ring.intCast_neg x
  | rw [Lean.Grind.Ring.intCast_neg]
  | grind

theorem hk_cast_mul (x y : Int) :
    (Int.cast (x * y) : K) = (Int.cast x : K) * (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_mul x y
  | rw [Lean.Grind.Ring.intCast_mul]
  | grind

theorem hk_cast_sub (x y : Int) :
    (Int.cast (x - y) : K) = (Int.cast x : K) - (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_sub x y
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)
  | grind

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first
  | exact Lean.Grind.Field.div_eq_mul_inv x y
  | rw [Lean.Grind.Field.div_eq_mul_inv]
  | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first
  | exact Lean.Grind.Field.mul_inv_cancel hx
  | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    have e : y = x⁻¹ * (x * y) + y * (1 - x * x⁻¹) := by grind
    rw [h, hinv] at e
    rw [e]
    grind

theorem hk_disc_cast (a b c : Int) :
    (Int.cast (hkDisc a b c) : K)
      = (Int.cast b : K) * (Int.cast b : K) - 4 * (Int.cast a : K) * (Int.cast c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (Int.cast a : K) ≠ 0 := by
  intro h
  have h2 : (Int.cast (a + a) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alg_alpha (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B + s) / (2 * A)) * ((-B + s) / (2 * A)) + B * ((-B + s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B + s) * w) * ((-B + s) * w) + B * ((-B + s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w - B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_beta (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B - s) / (2 * A)) * ((-B - s) / (2 * A)) + B * ((-B - s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B - s) * w) * ((-B - s) * w) + B * ((-B - s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w + B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_ne (A B s : K) (hA : 2 * A ≠ 0)
    (h : (-B + s) / (2 * A) = (-B - s) / (2 * A)) : s = 0 := by
  rw [hk_div, hk_div] at h
  have hw := hk_inv hA
  generalize (2 * A)⁻¹ = w at hw h
  have e : s = A * ((-B + s) * w - (-B - s) * w) + s * (1 - 2 * A * w) := by grind
  rw [h, hw] at e
  rw [e]
  grind

theorem hk_alg_sq (A B C x : K) (h : A * x * x + B * x + C = 0) :
    (2 * A * x + B) * (2 * A * x + B) = B * B - 4 * A * C := by
  have e : (2 * A * x + B) * (2 * A * x + B)
      = 4 * A * (A * x * x + B * x + C) + (B * B - 4 * A * C) := by grind
  rw [h] at e
  rw [e]
  grind

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkAlpha a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_alpha (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkBeta a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_beta (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have s0 := hk_alg_ne (Int.cast a) (Int.cast b) s (hk_two_a_ne a hchar ha) h
  apply hD
  apply hchar
  rw [← hs, s0]
  grind

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = (Int.cast (hkDisc a b c) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
      hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hq : (Int.cast (a + a) : K) = 2 * (Int.cast a : K) := by rw [hk_cast_add]; grind
  have hf : (s - (Int.cast k : K)) * (s + (Int.cast k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · have hsk : s = (Int.cast k : K) := by grind
    have h1 : (Int.cast (-b + k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    have h2 : (Int.cast (-b - k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]
  · have hsk : s = -(Int.cast k : K) := by grind
    have h1 : (Int.cast (-b - k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    have h2 : (Int.cast (-b + k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]

theorem hk_sq (O : HKOrd K) (y : K) : y * y = 0 ∨ O.pos (y * y) := by
  rcases O.trich y with hp | h0 | hn
  · exact Or.inr (O.pos_mul _ _ hp hp)
  · left
    rw [h0]
    grind
  · right
    have h := O.pos_mul _ _ hn hn
    have e : (-y) * (-y) = y * y := by grind
    rw [e] at h
    exact h

theorem hk_ord_two (O : HKOrd K) (x : K) (h : x + x = 0) : x = 0 := by
  rcases O.trich x with hp | h0 | hn
  · have h3 := O.pos_add _ _ hp hp
    rw [h] at h3
    exact absurd h3 O.not_pos_zero
  · exact h0
  · have h3 := O.pos_add _ _ hn hn
    have e1 : -x + -x = -(x + x) := by grind
    have e2 : -(x + x) = -(0 : K) := by rw [h]
    have e3 : -(0 : K) = 0 := by grind
    rw [e1, e2, e3] at h3
    exact absurd h3 O.not_pos_zero

theorem hk_two_ne (O : HKOrd K) (A : K) (hA : A ≠ 0) : 2 * A ≠ 0 := by
  intro h
  apply hA
  apply hk_ord_two O
  have e : A + A = 2 * A := by grind
  rw [e]
  exact h

theorem hk_realK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (B * B - 4 * A * C)) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
      hkAlphaK A B s ≠ hkBetaK A B s := by
  obtain ⟨s, hs⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  refine ⟨s, hs, hk_alg_alpha A B C s h2A hs, hk_alg_beta A B C s h2A hs, ?_⟩
  intro h
  have s0 := hk_alg_ne A B s h2A h
  have e : B * B - 4 * A * C = 0 := by rw [← hs, s0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_double_exK (O : HKOrd K) (A B C : K) (hA : A ≠ 0) (hD : B * B - 4 * A * C = 0) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) := by
  have h2A := hk_two_ne O A hA
  have hs : (0 : K) * 0 = B * B - 4 * A * C := by rw [hD]; grind
  exact ⟨0, hs, hk_alg_alpha A B C 0 h2A hs, hk_alg_beta A B C 0 h2A hs⟩

theorem hk_doubleK (A B C s : K) (hs : s * s = B * B - 4 * A * C)
    (hD : B * B - 4 * A * C = 0) :
    hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A) := by
  rw [hD] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  have e1 : -B + 0 = -B := by grind
  have e2 : -B - 0 = -B := by grind
  unfold hkAlphaK hkBetaK
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem hk_no_rootK (O : HKOrd K) (A B C : K) (hD : O.pos (-(B * B - 4 * A * C))) (x : K) :
    ¬ hkRootK A B C x := by
  intro h
  have e := hk_alg_sq A B C x h
  rcases hk_sq O (2 * A * x + B) with h0 | hp
  · rw [e] at h0
    rw [h0] at hD
    have e2 : -(0 : K) = 0 := by grind
    rw [e2] at hD
    exact O.not_pos_zero hD
  · rw [e] at hp
    have h3 := O.pos_add _ _ hp hD
    have e2 : (B * B - 4 * A * C) + -(B * B - 4 * A * C) = 0 := by grind
    rw [e2] at h3
    exact O.not_pos_zero h3

theorem hk_t_ne (O : HKOrd K) (D t : K) (hD : O.pos (-D)) (ht : t * t = -D) : t ≠ 0 := by
  intro h0
  have e : -D = 0 := by rw [← ht, h0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_croot_of (A B C p q : K) (h1 : A * p * p - A * q * q + B * p + C = 0)
    (h2 : 2 * A * p * q + B * q = 0) : hkCRoot A B C (p, q) := by
  unfold hkCRoot
  refine hk_pair_eq ?_ ?_
  · show (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C = 0
    have e : (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C
        = A * p * p - A * q * q + B * p + C := by grind
    exact e.trans h1
  · show (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0 = 0
    have e : (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0
        = 2 * A * p * q + B * q := by grind
    exact e.trans h2

theorem hk_calpha_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCAlpha A B t) := by
  have hw := hk_inv h2A
  unfold hkCAlpha
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (t * w) * (t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (t * w) + B * (t * w) = -(B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_cbeta_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCBeta A B t) := by
  have hw := hk_inv h2A
  unfold hkCBeta
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (-t * w) * (-t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (-t * w) + B * (-t * w) = (B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_calpha_ne (O : HKOrd K) (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) :
    hkCAlpha A B t ≠ hkCBeta A B t := by
  intro h
  have hq : t / (2 * A) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div, hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t + t = 2 * A * (t * w - -t * w) - (t + t) * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  have h3 : t * w - -t * w = 0 := by rw [hq]; grind
  rw [h1, h3] at e
  apply ht0
  apply hk_ord_two O
  exact e.trans (by grind)

theorem hk_calpha_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCAlpha A B t := by
  intro h
  have hq : (0 : K) = t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = 2 * A * (t * w) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_cbeta_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCBeta A B t := by
  intro h
  have hq : (0 : K) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = -(2 * A * (-t * w)) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_calpha_form (A B t : K) :
    hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * t)) * 0
    rw [hk_div]
    grind
  · show t / (2 * A) = (-B + (0 * t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_cbeta_form (A B t : K) :
    hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * -t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * -t)) * 0
    rw [hk_div]
    grind
  · show -t / (2 * A) = (-B + (0 * -t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * -t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_complexK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (-(B * B - 4 * A * C))) :
    ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
      hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
      hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
      hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
      hkCAlpha A B t ≠ hkCBeta A B t ∧
      (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t) := by
  obtain ⟨t, ht⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  have ht0 := hk_t_ne O _ t hD ht
  exact ⟨t, ht, hk_calpha_form A B t, hk_cbeta_form A B t, hk_calpha_root A B C t h2A ht,
    hk_cbeta_root A B C t h2A ht, hk_calpha_ne O A B t h2A ht0,
    fun x => hk_calpha_notreal A B t h2A ht0 x, fun x => hk_cbeta_notreal A B t h2A ht0 x⟩

theorem hk_i_sq : hkCMul (hkI : K × K) hkI = hkCOf (-1) := by
  refine hk_pair_eq ?_ ?_
  · show (0 : K) * 0 - 1 * 1 = -1
    grind
  · show (0 : K) * 1 + 1 * 0 = 0
    grind

theorem hk_cadd_assoc (z w v : K × K) :
    hkCAdd (hkCAdd z w) v = hkCAdd z (hkCAdd w v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show a + c + e = a + (c + e)
    grind
  · show b + d + f = b + (d + f)
    grind

theorem hk_cadd_comm (z w : K × K) : hkCAdd z w = hkCAdd w z := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  refine hk_pair_eq ?_ ?_
  · show a + c = c + a
    grind
  · show b + d = d + b
    grind

theorem hk_cadd_zero (z : K × K) : hkCAdd z (hkCOf 0) = z := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a + 0 = a
    grind
  · show b + 0 = b
    grind

theorem hk_cadd_neg (z : K × K) : hkCAdd z (-z.1, -z.2) = hkCOf 0 := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a + -a = 0
    grind
  · show b + -b = 0
    grind

theorem hk_cmul_assoc (z w v : K × K) :
    hkCMul (hkCMul z w) v = hkCMul z (hkCMul w v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show (a * c - b * d) * e - (a * d + b * c) * f
        = a * (c * e - d * f) - b * (c * f + d * e)
    grind
  · show (a * c - b * d) * f + (a * d + b * c) * e
        = a * (c * f + d * e) + b * (c * e - d * f)
    grind

theorem hk_cmul_comm (z w : K × K) : hkCMul z w = hkCMul w z := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  refine hk_pair_eq ?_ ?_
  · show a * c - b * d = c * a - d * b
    grind
  · show a * d + b * c = c * b + d * a
    grind

theorem hk_cmul_one (z : K × K) : hkCMul z (hkCOf 1) = z := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a * 1 - b * 0 = a
    grind
  · show a * 0 + b * 1 = b
    grind

theorem hk_cmul_add (z w v : K × K) :
    hkCMul z (hkCAdd w v) = hkCAdd (hkCMul z w) (hkCMul z v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show a * (c + e) - b * (d + f) = (a * c - b * d) + (a * e - b * f)
    grind
  · show a * (d + f) + b * (c + e) = (a * d + b * c) + (a * f + b * e)
    grind

theorem hk_cone_ne (O : HKOrd K) : hkCOf (1 : K) ≠ hkCOf 0 := by
  intro h
  have h1 : (1 : K) = 0 := congrArg Prod.fst h
  have hp := O.pos_one
  rw [h1] at hp
  exact O.not_pos_zero hp

theorem hk_cof_add (x y : K) : hkCOf (x + y) = hkCAdd (hkCOf x) (hkCOf y) := by
  refine hk_pair_eq ?_ ?_
  · show x + y = x + y
    rfl
  · show (0 : K) = 0 + 0
    grind

theorem hk_cof_mul (x y : K) : hkCOf (x * y) = hkCMul (hkCOf x) (hkCOf y) := by
  refine hk_pair_eq ?_ ?_
  · show x * y = x * y - 0 * 0
    grind
  · show (0 : K) = x * 0 + 0 * y
    grind

theorem hk_sumsq (O : HKOrd K) (x y : K) (h : x * x + y * y = 0) : x = 0 ∧ y = 0 := by
  have hx : x * x = 0 := by
    rcases hk_sq O x with hx0 | hxp
    · exact hx0
    · rcases hk_sq O y with hy0 | hyp
      · rw [hy0] at h
        have e : x * x + 0 = x * x := by grind
        rw [e] at h
        exact h
      · have h3 := O.pos_add _ _ hxp hyp
        rw [h] at h3
        exact absurd h3 O.not_pos_zero
  have hy : y * y = 0 := by
    rw [hx] at h
    have e : 0 + y * y = y * y := by grind
    rw [e] at h
    exact h
  constructor
  · rcases hk_mul_zero hx with h1 | h1 <;> exact h1
  · rcases hk_mul_zero hy with h1 | h1 <;> exact h1

theorem hk_cinv (O : HKOrd K) (x y : K) (hz : (x, y) ≠ hkCOf 0) :
    ∃ w : K × K, hkCMul (x, y) w = hkCOf 1 := by
  have hn : x * x + y * y ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := hk_sumsq O x y h
    subst h1
    subst h2
    exact hz rfl
  have hm := hk_inv hn
  refine ⟨(x * (x * x + y * y)⁻¹, -(y * (x * x + y * y)⁻¹)), ?_⟩
  generalize (x * x + y * y)⁻¹ = m at hm ⊢
  refine hk_pair_eq ?_ ?_
  · show x * (x * m) - y * -(y * m) = 1
    have e : x * (x * m) - y * -(y * m) = (x * x + y * y) * m := by grind
    exact e.trans hm
  · show x * -(y * m) + y * (x * m) = 0
    grind

end HKField

/-- Hall and Knight, Art. 113. Take `A x² + B x + C = 0` with `A ≠ 0`, put `D = B² − 4AC`,
`α = (−B + √D)/(2A)` and `β = (−B − √D)/(2A)`. Real coefficients are modelled by an ordered field
`K` (an `HKOrd K`) in which every positive element has a square root, as in ℝ.
(1) If `D > 0`, then `√D` exists in `K`, and α, β are real roots that are unequal.
(2) If `D = 0`, then α and β are real roots, and for every square root of `D` both reduce to
`−B/(2A)`.
(3) If `D < 0`, then no element of `K` is a root. `K × K` with `i² = −1` is a field extension of
`K`: addition and multiplication are associative and commutative, have neutral elements and
satisfy distributivity, additive and multiplicative inverses exist, `1 ≠ 0`, and `x ↦ (x, 0)`
preserves sums and products. There the numbers `(−B ± i t)/(2A)` with `t² = −D` are roots. They
are unequal, and neither lies in the image of `K`, so both are imaginary.
(4) For integer coefficients, in any field of characteristic zero, α and β (with `s² = D`) are
roots, and they are unequal when `D ≠ 0`. If `D = k²`, such an `s` exists, and α, β are
quotients of integers. -/
theorem hk_art_113 :
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      (∀ x : K, O.pos x → ∃ s : K, s * s = x) →
      ∀ A B C : K, A ≠ 0 →
        (O.pos (B * B - 4 * A * C) →
          ∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
            hkAlphaK A B s ≠ hkBetaK A B s) ∧
        (B * B - 4 * A * C = 0 →
          (∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s)) ∧
          ∀ s : K, s * s = B * B - 4 * A * C →
            hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A)) ∧
        (O.pos (-(B * B - 4 * A * C)) →
          (∀ x : K, ¬ hkRootK A B C x) ∧
          ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
            hkCAlpha A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
            hkCBeta A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
            hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
            hkCAlpha A B t ≠ hkCBeta A B t ∧
            (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t))) ∧
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      hkCMul (hkI : K × K) hkI = hkCOf (-1) ∧
      (∀ z w v : K × K, hkCAdd (hkCAdd z w) v = hkCAdd z (hkCAdd w v)) ∧
      (∀ z w : K × K, hkCAdd z w = hkCAdd w z) ∧
      (∀ z : K × K, hkCAdd z (hkCOf 0) = z) ∧
      (∀ z : K × K, hkCAdd z (-z.1, -z.2) = hkCOf 0) ∧
      (∀ z w v : K × K, hkCMul (hkCMul z w) v = hkCMul z (hkCMul w v)) ∧
      (∀ z w : K × K, hkCMul z w = hkCMul w z) ∧
      (∀ z : K × K, hkCMul z (hkCOf 1) = z) ∧
      (∀ z w v : K × K, hkCMul z (hkCAdd w v) = hkCAdd (hkCMul z w) (hkCMul z v)) ∧
      hkCOf (1 : K) ≠ hkCOf 0 ∧
      (∀ x y : K, hkCOf (x + y) = hkCAdd (hkCOf x) (hkCOf y)) ∧
      (∀ x y : K, hkCOf (x * y) = hkCMul (hkCOf x) (hkCOf y)) ∧
      ∀ x y : K, (x, y) ≠ hkCOf 0 → ∃ w : K × K, hkCMul (x, y) w = hkCOf 1) ∧
    (∀ a b c : Int, a ≠ 0 →
      ∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
        ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
          hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
          (hkDisc a b c ≠ 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
          (∀ k : Int, hkDisc a b c = k * k →
            ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
              hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K))) ∧
    (∀ a b c k : Int, hkDisc a b c = k * k →
      ∀ (K : Type) [Lean.Grind.Field K], ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K inst O hsqrt A B C hA
    exact ⟨fun hD => hk_realK O hsqrt A B C hA hD,
      fun hD => ⟨hk_double_exK O A B C hA hD, fun s hs => hk_doubleK A B C s hs hD⟩,
      fun hD => ⟨fun x => hk_no_rootK O A B C hD x, hk_complexK O hsqrt A B C hA hD⟩⟩
  · intro K inst O
    exact ⟨hk_i_sq, hk_cadd_assoc, hk_cadd_comm, hk_cadd_zero, hk_cadd_neg, hk_cmul_assoc,
      hk_cmul_comm, hk_cmul_one, hk_cmul_add, hk_cone_ne O, hk_cof_add, hk_cof_mul,
      fun x y hz => hk_cinv O x y hz⟩
  · intro a b c ha K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs hD, fun k hk => hk_rational a b c ha s hs k hk⟩
  · intro a b c k hk K inst
    refine ⟨Int.cast k, ?_⟩
    rw [hk, hk_cast_mul]

## lean
Lean accepts the code.

## challenger
**NO OBJECTION.** Lean accepts the code, and `hk_art_113` no longer depends on `sorry`.

- **Field laws:** My last objection is answered. `K × K` with `i² = −1` now has associativity, commutativity, neutral elements and distributivity proved for both operations, along with additive and multiplicative inverses and `1 ≠ 0`. The embedding `x ↦ (x, 0)` is shown to preserve sums and products. This makes it a genuine field extension of `K`, even though no `Lean.Grind.Field` instance is registered.
- **Cases (1)–(3):** They now hold for coefficients in an ordered field with square roots of positive elements.
  - Case (3) proves that no element of `K` is a root.
  - The roots `(−B ± i t)/(2A)` exist in the extension, are unequal, and lie outside the image of `K`.
- **Case (4):** It keeps integer coefficients and states `D ≠ 0`, both of which the supervisor endorsed.
- **Remaining point:** The only open issue is the hypothesis-based treatment of ℝ. The supervisor explicitly accepted that, so I have no further objection I can defend.

## prover
-- No objection remains open, so the code is unchanged from the version Lean accepted.
-- * Cases (1)–(3) are stated for coefficients in an ordered field `K` in which every positive
--   element has a square root, as in ℝ. Core Lean has no ℝ, so this is a hypothesis.
-- * Case (3) builds the extension `K × K` with `i² = −1` and proves its field laws as plain
--   lemmas. It is not registered as a `Lean.Grind.Field` instance.
-- * Case (4) keeps integer coefficients. It also keeps `D ≠ 0`, because `D = 0 = 0²` gives
--   equal roots by case (2).

attribute [local instance] Lean.Grind.Ring.intCast

/-- The quantity under the radical, `b² − 4ac`. -/
def hkDisc (a b c : Int) : Int := b * b - 4 * a * c

universe u v

/-- An ordered field, given by its positive cone. -/
structure HKOrd (K : Type u) [Lean.Grind.Field K] where
  pos : K → Prop
  pos_add : ∀ x y : K, pos x → pos y → pos (x + y)
  pos_mul : ∀ x y : K, pos x → pos y → pos (x * y)
  pos_one : pos 1
  trich : ∀ x : K, pos x ∨ x = 0 ∨ pos (-x)
  not_pos_zero : ¬ pos 0

theorem hk_pair_eq {α : Type u} {β : Type v} {a c : α} {b d : β} (h1 : a = c) (h2 : b = d) :
    (a, b) = (c, d) := by
  rw [h1, h2]

section HKField
variable {K : Type u} [Lean.Grind.Field K]

/-- The root `α = (−b + s)/(2a)` for integer coefficients. -/
def hkAlpha (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) + s) / (2 * (Int.cast a : K))

/-- The root `β = (−b − s)/(2a)` for integer coefficients. -/
def hkBeta (a b : Int) (s : K) : K :=
  (-(Int.cast b : K) - s) / (2 * (Int.cast a : K))

/-- `x` satisfies `a x² + b x + c = 0` in `K`, with integer coefficients. -/
def hkRoot (a b c : Int) (x : K) : Prop :=
  (Int.cast a : K) * x * x + (Int.cast b : K) * x + (Int.cast c : K) = 0

/-- `x` satisfies `A x² + B x + C = 0`, with coefficients in `K`. -/
def hkRootK (A B C x : K) : Prop := A * x * x + B * x + C = 0

/-- `α = (−B + s)/(2A)`. -/
def hkAlphaK (A B s : K) : K := (-B + s) / (2 * A)

/-- `β = (−B − s)/(2A)`. -/
def hkBetaK (A B s : K) : K := (-B - s) / (2 * A)

/-- Addition in the extension `K × K` (elements `x + i y`). -/
def hkCAdd (z w : K × K) : K × K := (z.1 + w.1, z.2 + w.2)

/-- Multiplication in the extension `K × K`, with `i² = −1`. -/
def hkCMul (z w : K × K) : K × K := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- The embedding `x ↦ x + 0 i` of `K`. -/
def hkCOf (x : K) : K × K := (x, 0)

/-- The imaginary unit `i`. -/
def hkI : K × K := (0, 1)

/-- `z` satisfies `A z² + B z + C = 0` in the extension. -/
def hkCRoot (A B C : K) (z : K × K) : Prop :=
  hkCAdd (hkCAdd (hkCMul (hkCMul (hkCOf A) z) z) (hkCMul (hkCOf B) z)) (hkCOf C) = hkCOf 0

/-- The root `(−B + i t)/(2A)`. -/
def hkCAlpha (A B t : K) : K × K := (-B / (2 * A), t / (2 * A))

/-- The root `(−B − i t)/(2A)`. -/
def hkCBeta (A B t : K) : K × K := (-B / (2 * A), -t / (2 * A))

theorem hk_cast_add (x y : Int) :
    (Int.cast (x + y) : K) = (Int.cast x : K) + (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_add x y
  | rw [Lean.Grind.Ring.intCast_add]
  | grind

theorem hk_cast_neg (x : Int) : (Int.cast (-x) : K) = -(Int.cast x : K) := by
  first
  | exact Lean.Grind.Ring.intCast_neg x
  | rw [Lean.Grind.Ring.intCast_neg]
  | grind

theorem hk_cast_mul (x y : Int) :
    (Int.cast (x * y) : K) = (Int.cast x : K) * (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_mul x y
  | rw [Lean.Grind.Ring.intCast_mul]
  | grind

theorem hk_cast_sub (x y : Int) :
    (Int.cast (x - y) : K) = (Int.cast x : K) - (Int.cast y : K) := by
  first
  | exact Lean.Grind.Ring.intCast_sub x y
  | (rw [Int.sub_eq_add_neg, hk_cast_add, hk_cast_neg]; grind)
  | grind

theorem hk_div (x y : K) : x / y = x * y⁻¹ := by
  first
  | exact Lean.Grind.Field.div_eq_mul_inv x y
  | rw [Lean.Grind.Field.div_eq_mul_inv]
  | grind

theorem hk_inv {x : K} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  first
  | exact Lean.Grind.Field.mul_inv_cancel hx
  | grind

theorem hk_mul_zero {x y : K} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    have hinv := hk_inv hx
    have e : y = x⁻¹ * (x * y) + y * (1 - x * x⁻¹) := by grind
    rw [h, hinv] at e
    rw [e]
    grind

theorem hk_disc_cast (a b c : Int) :
    (Int.cast (hkDisc a b c) : K)
      = (Int.cast b : K) * (Int.cast b : K) - 4 * (Int.cast a : K) * (Int.cast c : K) := by
  have e : hkDisc a b c = b * b - (a + a) * (c + c) := by unfold hkDisc; grind
  rw [e]
  simp only [hk_cast_sub, hk_cast_mul, hk_cast_add]
  grind

theorem hk_two_a_ne (a : Int) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0) (ha : a ≠ 0) :
    2 * (Int.cast a : K) ≠ 0 := by
  intro h
  have h2 : (Int.cast (a + a) : K) = 0 := by rw [hk_cast_add]; grind
  have := hchar _ h2
  omega

theorem hk_alg_alpha (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B + s) / (2 * A)) * ((-B + s) / (2 * A)) + B * ((-B + s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B + s) * w) * ((-B + s) * w) + B * ((-B + s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w - B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_beta (A B C s : K) (hA : 2 * A ≠ 0) (hs : s * s = B * B - 4 * A * C) :
    A * ((-B - s) / (2 * A)) * ((-B - s) / (2 * A)) + B * ((-B - s) / (2 * A)) + C = 0 := by
  have hw := hk_inv hA
  rw [hk_div]
  generalize (2 * A)⁻¹ = w at hw ⊢
  have e : A * ((-B - s) * w) * ((-B - s) * w) + B * ((-B - s) * w) + C
      = A * w * w * (s * s - (B * B - 4 * A * C))
        + (2 * A * w - 1) * (B * B * w + B * s * w - C * (2 * A * w + 1)) := by grind
  have h1 : s * s - (B * B - 4 * A * C) = 0 := by rw [hs]; grind
  have h2 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [e, h1, h2]
  grind

theorem hk_alg_ne (A B s : K) (hA : 2 * A ≠ 0)
    (h : (-B + s) / (2 * A) = (-B - s) / (2 * A)) : s = 0 := by
  rw [hk_div, hk_div] at h
  have hw := hk_inv hA
  generalize (2 * A)⁻¹ = w at hw h
  have e : s = A * ((-B + s) * w - (-B - s) * w) + s * (1 - 2 * A * w) := by grind
  rw [h, hw] at e
  rw [e]
  grind

theorem hk_alg_sq (A B C x : K) (h : A * x * x + B * x + C = 0) :
    (2 * A * x + B) * (2 * A * x + B) = B * B - 4 * A * C := by
  have e : (2 * A * x + B) * (2 * A * x + B)
      = 4 * A * (A * x * x + B * x + C) + (B * B - 4 * A * C) := by grind
  rw [h] at e
  rw [e]
  grind

theorem hk_alpha_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkAlpha a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_alpha (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_beta_root (a b c : Int) (ha : a ≠ 0)
    (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) : hkRoot a b c (hkBeta a b s) := by
  rw [hk_disc_cast] at hs
  exact hk_alg_beta (Int.cast a) (Int.cast b) (Int.cast c) s (hk_two_a_ne a hchar ha) hs

theorem hk_ne (a b c : Int) (ha : a ≠ 0) (hchar : ∀ n : Int, (Int.cast n : K) = 0 → n = 0)
    (s : K) (hs : s * s = (Int.cast (hkDisc a b c) : K)) (hD : hkDisc a b c ≠ 0) :
    hkAlpha a b s ≠ hkBeta a b s := by
  intro h
  have s0 := hk_alg_ne (Int.cast a) (Int.cast b) s (hk_two_a_ne a hchar ha) h
  apply hD
  apply hchar
  rw [← hs, s0]
  grind

theorem hk_rational (a b c : Int) (ha : a ≠ 0) (s : K)
    (hs : s * s = (Int.cast (hkDisc a b c) : K)) (k : Int) (hk : hkDisc a b c = k * k) :
    ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
      hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K) := by
  rw [hk, hk_cast_mul] at hs
  have hq : (Int.cast (a + a) : K) = 2 * (Int.cast a : K) := by rw [hk_cast_add]; grind
  have hf : (s - (Int.cast k : K)) * (s + (Int.cast k : K)) = 0 := by grind
  rcases hk_mul_zero hf with h | h
  · have hsk : s = (Int.cast k : K) := by grind
    have h1 : (Int.cast (-b + k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    have h2 : (Int.cast (-b - k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    refine ⟨-b + k, -b - k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]
  · have hsk : s = -(Int.cast k : K) := by grind
    have h1 : (Int.cast (-b - k) : K) = -(Int.cast b : K) + s := by
      rw [hk_cast_sub, hk_cast_neg]; grind
    have h2 : (Int.cast (-b + k) : K) = -(Int.cast b : K) - s := by
      rw [hk_cast_add, hk_cast_neg]; grind
    refine ⟨-b - k, -b + k, a + a, by omega, ?_, ?_⟩
    · unfold hkAlpha; rw [h1, hq]
    · unfold hkBeta; rw [h2, hq]

theorem hk_sq (O : HKOrd K) (y : K) : y * y = 0 ∨ O.pos (y * y) := by
  rcases O.trich y with hp | h0 | hn
  · exact Or.inr (O.pos_mul _ _ hp hp)
  · left
    rw [h0]
    grind
  · right
    have h := O.pos_mul _ _ hn hn
    have e : (-y) * (-y) = y * y := by grind
    rw [e] at h
    exact h

theorem hk_ord_two (O : HKOrd K) (x : K) (h : x + x = 0) : x = 0 := by
  rcases O.trich x with hp | h0 | hn
  · have h3 := O.pos_add _ _ hp hp
    rw [h] at h3
    exact absurd h3 O.not_pos_zero
  · exact h0
  · have h3 := O.pos_add _ _ hn hn
    have e1 : -x + -x = -(x + x) := by grind
    have e2 : -(x + x) = -(0 : K) := by rw [h]
    have e3 : -(0 : K) = 0 := by grind
    rw [e1, e2, e3] at h3
    exact absurd h3 O.not_pos_zero

theorem hk_two_ne (O : HKOrd K) (A : K) (hA : A ≠ 0) : 2 * A ≠ 0 := by
  intro h
  apply hA
  apply hk_ord_two O
  have e : A + A = 2 * A := by grind
  rw [e]
  exact h

theorem hk_realK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (B * B - 4 * A * C)) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
      hkAlphaK A B s ≠ hkBetaK A B s := by
  obtain ⟨s, hs⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  refine ⟨s, hs, hk_alg_alpha A B C s h2A hs, hk_alg_beta A B C s h2A hs, ?_⟩
  intro h
  have s0 := hk_alg_ne A B s h2A h
  have e : B * B - 4 * A * C = 0 := by rw [← hs, s0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_double_exK (O : HKOrd K) (A B C : K) (hA : A ≠ 0) (hD : B * B - 4 * A * C = 0) :
    ∃ s : K, s * s = B * B - 4 * A * C ∧
      hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) := by
  have h2A := hk_two_ne O A hA
  have hs : (0 : K) * 0 = B * B - 4 * A * C := by rw [hD]; grind
  exact ⟨0, hs, hk_alg_alpha A B C 0 h2A hs, hk_alg_beta A B C 0 h2A hs⟩

theorem hk_doubleK (A B C s : K) (hs : s * s = B * B - 4 * A * C)
    (hD : B * B - 4 * A * C = 0) :
    hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A) := by
  rw [hD] at hs
  have hs0 : s = 0 := by rcases hk_mul_zero hs with h | h <;> exact h
  subst hs0
  have e1 : -B + 0 = -B := by grind
  have e2 : -B - 0 = -B := by grind
  unfold hkAlphaK hkBetaK
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

theorem hk_no_rootK (O : HKOrd K) (A B C : K) (hD : O.pos (-(B * B - 4 * A * C))) (x : K) :
    ¬ hkRootK A B C x := by
  intro h
  have e := hk_alg_sq A B C x h
  rcases hk_sq O (2 * A * x + B) with h0 | hp
  · rw [e] at h0
    rw [h0] at hD
    have e2 : -(0 : K) = 0 := by grind
    rw [e2] at hD
    exact O.not_pos_zero hD
  · rw [e] at hp
    have h3 := O.pos_add _ _ hp hD
    have e2 : (B * B - 4 * A * C) + -(B * B - 4 * A * C) = 0 := by grind
    rw [e2] at h3
    exact O.not_pos_zero h3

theorem hk_t_ne (O : HKOrd K) (D t : K) (hD : O.pos (-D)) (ht : t * t = -D) : t ≠ 0 := by
  intro h0
  have e : -D = 0 := by rw [← ht, h0]; grind
  rw [e] at hD
  exact O.not_pos_zero hD

theorem hk_croot_of (A B C p q : K) (h1 : A * p * p - A * q * q + B * p + C = 0)
    (h2 : 2 * A * p * q + B * q = 0) : hkCRoot A B C (p, q) := by
  unfold hkCRoot
  refine hk_pair_eq ?_ ?_
  · show (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C = 0
    have e : (A * p - 0 * q) * p - (A * q + 0 * p) * q + (B * p - 0 * q) + C
        = A * p * p - A * q * q + B * p + C := by grind
    exact e.trans h1
  · show (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0 = 0
    have e : (A * p - 0 * q) * q + (A * q + 0 * p) * p + (B * q + 0 * p) + 0
        = 2 * A * p * q + B * q := by grind
    exact e.trans h2

theorem hk_calpha_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCAlpha A B t) := by
  have hw := hk_inv h2A
  unfold hkCAlpha
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (t * w) * (t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (t * w) + B * (t * w) = -(B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_cbeta_root (A B C t : K) (h2A : 2 * A ≠ 0) (ht : t * t = -(B * B - 4 * A * C)) :
    hkCRoot A B C (hkCBeta A B t) := by
  have hw := hk_inv h2A
  unfold hkCBeta
  apply hk_croot_of
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : A * (-B * w) * (-B * w) - A * (-t * w) * (-t * w) + B * (-B * w) + C
        = B * B * w * (2 * A * w - 1) - C * (2 * A * w + 1) * (2 * A * w - 1)
          - A * w * w * (t * t + (B * B - 4 * A * C)) := by grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    have h2 : t * t + (B * B - 4 * A * C) = 0 := by rw [ht]; grind
    rw [h1, h2] at e
    exact e.trans (by grind)
  · rw [hk_div, hk_div]
    generalize (2 * A)⁻¹ = w at hw ⊢
    have e : 2 * A * (-B * w) * (-t * w) + B * (-t * w) = (B * t * w) * (2 * A * w - 1) := by
      grind
    have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
    rw [h1] at e
    exact e.trans (by grind)

theorem hk_calpha_ne (O : HKOrd K) (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) :
    hkCAlpha A B t ≠ hkCBeta A B t := by
  intro h
  have hq : t / (2 * A) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div, hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t + t = 2 * A * (t * w - -t * w) - (t + t) * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  have h3 : t * w - -t * w = 0 := by rw [hq]; grind
  rw [h1, h3] at e
  apply ht0
  apply hk_ord_two O
  exact e.trans (by grind)

theorem hk_calpha_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCAlpha A B t := by
  intro h
  have hq : (0 : K) = t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = 2 * A * (t * w) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_cbeta_notreal (A B t : K) (h2A : 2 * A ≠ 0) (ht0 : t ≠ 0) (x : K) :
    hkCOf x ≠ hkCBeta A B t := by
  intro h
  have hq : (0 : K) = -t / (2 * A) := congrArg Prod.snd h
  have hw := hk_inv h2A
  rw [hk_div] at hq
  generalize (2 * A)⁻¹ = w at hw hq
  have e : t = -(2 * A * (-t * w)) - t * (2 * A * w - 1) := by grind
  have h1 : 2 * A * w - 1 = 0 := by rw [hw]; grind
  rw [← hq, h1] at e
  exact ht0 (e.trans (by grind))

theorem hk_calpha_form (A B t : K) :
    hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * t)) * 0
    rw [hk_div]
    grind
  · show t / (2 * A) = (-B + (0 * t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_cbeta_form (A B t : K) :
    hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) := by
  refine hk_pair_eq ?_ ?_
  · show -B / (2 * A) = (-B + (0 * -t - 1 * 0)) * (2 * A)⁻¹ - (0 + (0 * 0 + 1 * -t)) * 0
    rw [hk_div]
    grind
  · show -t / (2 * A) = (-B + (0 * -t - 1 * 0)) * 0 + (0 + (0 * 0 + 1 * -t)) * (2 * A)⁻¹
    rw [hk_div]
    grind

theorem hk_complexK (O : HKOrd K) (hsqrt : ∀ x : K, O.pos x → ∃ s : K, s * s = x)
    (A B C : K) (hA : A ≠ 0) (hD : O.pos (-(B * B - 4 * A * C))) :
    ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
      hkCAlpha A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
      hkCBeta A B t = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
      hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
      hkCAlpha A B t ≠ hkCBeta A B t ∧
      (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t) := by
  obtain ⟨t, ht⟩ := hsqrt _ hD
  have h2A := hk_two_ne O A hA
  have ht0 := hk_t_ne O _ t hD ht
  exact ⟨t, ht, hk_calpha_form A B t, hk_cbeta_form A B t, hk_calpha_root A B C t h2A ht,
    hk_cbeta_root A B C t h2A ht, hk_calpha_ne O A B t h2A ht0,
    fun x => hk_calpha_notreal A B t h2A ht0 x, fun x => hk_cbeta_notreal A B t h2A ht0 x⟩

theorem hk_i_sq : hkCMul (hkI : K × K) hkI = hkCOf (-1) := by
  refine hk_pair_eq ?_ ?_
  · show (0 : K) * 0 - 1 * 1 = -1
    grind
  · show (0 : K) * 1 + 1 * 0 = 0
    grind

theorem hk_cadd_assoc (z w v : K × K) :
    hkCAdd (hkCAdd z w) v = hkCAdd z (hkCAdd w v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show a + c + e = a + (c + e)
    grind
  · show b + d + f = b + (d + f)
    grind

theorem hk_cadd_comm (z w : K × K) : hkCAdd z w = hkCAdd w z := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  refine hk_pair_eq ?_ ?_
  · show a + c = c + a
    grind
  · show b + d = d + b
    grind

theorem hk_cadd_zero (z : K × K) : hkCAdd z (hkCOf 0) = z := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a + 0 = a
    grind
  · show b + 0 = b
    grind

theorem hk_cadd_neg (z : K × K) : hkCAdd z (-z.1, -z.2) = hkCOf 0 := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a + -a = 0
    grind
  · show b + -b = 0
    grind

theorem hk_cmul_assoc (z w v : K × K) :
    hkCMul (hkCMul z w) v = hkCMul z (hkCMul w v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show (a * c - b * d) * e - (a * d + b * c) * f
        = a * (c * e - d * f) - b * (c * f + d * e)
    grind
  · show (a * c - b * d) * f + (a * d + b * c) * e
        = a * (c * f + d * e) + b * (c * e - d * f)
    grind

theorem hk_cmul_comm (z w : K × K) : hkCMul z w = hkCMul w z := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  refine hk_pair_eq ?_ ?_
  · show a * c - b * d = c * a - d * b
    grind
  · show a * d + b * c = c * b + d * a
    grind

theorem hk_cmul_one (z : K × K) : hkCMul z (hkCOf 1) = z := by
  obtain ⟨a, b⟩ := z
  refine hk_pair_eq ?_ ?_
  · show a * 1 - b * 0 = a
    grind
  · show a * 0 + b * 1 = b
    grind

theorem hk_cmul_add (z w v : K × K) :
    hkCMul z (hkCAdd w v) = hkCAdd (hkCMul z w) (hkCMul z v) := by
  obtain ⟨a, b⟩ := z
  obtain ⟨c, d⟩ := w
  obtain ⟨e, f⟩ := v
  refine hk_pair_eq ?_ ?_
  · show a * (c + e) - b * (d + f) = (a * c - b * d) + (a * e - b * f)
    grind
  · show a * (d + f) + b * (c + e) = (a * d + b * c) + (a * f + b * e)
    grind

theorem hk_cone_ne (O : HKOrd K) : hkCOf (1 : K) ≠ hkCOf 0 := by
  intro h
  have h1 : (1 : K) = 0 := congrArg Prod.fst h
  have hp := O.pos_one
  rw [h1] at hp
  exact O.not_pos_zero hp

theorem hk_cof_add (x y : K) : hkCOf (x + y) = hkCAdd (hkCOf x) (hkCOf y) := by
  refine hk_pair_eq ?_ ?_
  · show x + y = x + y
    rfl
  · show (0 : K) = 0 + 0
    grind

theorem hk_cof_mul (x y : K) : hkCOf (x * y) = hkCMul (hkCOf x) (hkCOf y) := by
  refine hk_pair_eq ?_ ?_
  · show x * y = x * y - 0 * 0
    grind
  · show (0 : K) = x * 0 + 0 * y
    grind

theorem hk_sumsq (O : HKOrd K) (x y : K) (h : x * x + y * y = 0) : x = 0 ∧ y = 0 := by
  have hx : x * x = 0 := by
    rcases hk_sq O x with hx0 | hxp
    · exact hx0
    · rcases hk_sq O y with hy0 | hyp
      · rw [hy0] at h
        have e : x * x + 0 = x * x := by grind
        rw [e] at h
        exact h
      · have h3 := O.pos_add _ _ hxp hyp
        rw [h] at h3
        exact absurd h3 O.not_pos_zero
  have hy : y * y = 0 := by
    rw [hx] at h
    have e : 0 + y * y = y * y := by grind
    rw [e] at h
    exact h
  constructor
  · rcases hk_mul_zero hx with h1 | h1 <;> exact h1
  · rcases hk_mul_zero hy with h1 | h1 <;> exact h1

theorem hk_cinv (O : HKOrd K) (x y : K) (hz : (x, y) ≠ hkCOf 0) :
    ∃ w : K × K, hkCMul (x, y) w = hkCOf 1 := by
  have hn : x * x + y * y ≠ 0 := by
    intro h
    obtain ⟨h1, h2⟩ := hk_sumsq O x y h
    subst h1
    subst h2
    exact hz rfl
  have hm := hk_inv hn
  refine ⟨(x * (x * x + y * y)⁻¹, -(y * (x * x + y * y)⁻¹)), ?_⟩
  generalize (x * x + y * y)⁻¹ = m at hm ⊢
  refine hk_pair_eq ?_ ?_
  · show x * (x * m) - y * -(y * m) = 1
    have e : x * (x * m) - y * -(y * m) = (x * x + y * y) * m := by grind
    exact e.trans hm
  · show x * -(y * m) + y * (x * m) = 0
    grind

end HKField

/-- Hall and Knight, Art. 113. Take `A x² + B x + C = 0` with `A ≠ 0`, put `D = B² − 4AC`,
`α = (−B + √D)/(2A)` and `β = (−B − √D)/(2A)`. Real coefficients are modelled by an ordered field
`K` (an `HKOrd K`) in which every positive element has a square root, as in ℝ.
(1) If `D > 0`, then `√D` exists in `K`, and α, β are real roots that are unequal.
(2) If `D = 0`, then α and β are real roots, and for every square root of `D` both reduce to
`−B/(2A)`.
(3) If `D < 0`, then no element of `K` is a root. `K × K` with `i² = −1` is a field extension of
`K`: addition and multiplication are associative and commutative, have neutral elements and
satisfy distributivity, additive and multiplicative inverses exist, `1 ≠ 0`, and `x ↦ (x, 0)`
preserves sums and products. There the numbers `(−B ± i t)/(2A)` with `t² = −D` are roots. They
are unequal, and neither lies in the image of `K`, so both are imaginary.
(4) For integer coefficients, in any field of characteristic zero, α and β (with `s² = D`) are
roots, and they are unequal when `D ≠ 0`. If `D = k²`, such an `s` exists, and α, β are
quotients of integers. -/
theorem hk_art_113 :
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      (∀ x : K, O.pos x → ∃ s : K, s * s = x) →
      ∀ A B C : K, A ≠ 0 →
        (O.pos (B * B - 4 * A * C) →
          ∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s) ∧
            hkAlphaK A B s ≠ hkBetaK A B s) ∧
        (B * B - 4 * A * C = 0 →
          (∃ s : K, s * s = B * B - 4 * A * C ∧
            hkRootK A B C (hkAlphaK A B s) ∧ hkRootK A B C (hkBetaK A B s)) ∧
          ∀ s : K, s * s = B * B - 4 * A * C →
            hkAlphaK A B s = -B / (2 * A) ∧ hkBetaK A B s = -B / (2 * A)) ∧
        (O.pos (-(B * B - 4 * A * C)) →
          (∀ x : K, ¬ hkRootK A B C x) ∧
          ∃ t : K, t * t = -(B * B - 4 * A * C) ∧
            hkCAlpha A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf t))) (hkCOf (2 * A)⁻¹) ∧
            hkCBeta A B t
              = hkCMul (hkCAdd (hkCOf (-B)) (hkCMul hkI (hkCOf (-t)))) (hkCOf (2 * A)⁻¹) ∧
            hkCRoot A B C (hkCAlpha A B t) ∧ hkCRoot A B C (hkCBeta A B t) ∧
            hkCAlpha A B t ≠ hkCBeta A B t ∧
            (∀ x : K, hkCOf x ≠ hkCAlpha A B t) ∧ (∀ x : K, hkCOf x ≠ hkCBeta A B t))) ∧
    (∀ (K : Type) [Lean.Grind.Field K] (O : HKOrd K),
      hkCMul (hkI : K × K) hkI = hkCOf (-1) ∧
      (∀ z w v : K × K, hkCAdd (hkCAdd z w) v = hkCAdd z (hkCAdd w v)) ∧
      (∀ z w : K × K, hkCAdd z w = hkCAdd w z) ∧
      (∀ z : K × K, hkCAdd z (hkCOf 0) = z) ∧
      (∀ z : K × K, hkCAdd z (-z.1, -z.2) = hkCOf 0) ∧
      (∀ z w v : K × K, hkCMul (hkCMul z w) v = hkCMul z (hkCMul w v)) ∧
      (∀ z w : K × K, hkCMul z w = hkCMul w z) ∧
      (∀ z : K × K, hkCMul z (hkCOf 1) = z) ∧
      (∀ z w v : K × K, hkCMul z (hkCAdd w v) = hkCAdd (hkCMul z w) (hkCMul z v)) ∧
      hkCOf (1 : K) ≠ hkCOf 0 ∧
      (∀ x y : K, hkCOf (x + y) = hkCAdd (hkCOf x) (hkCOf y)) ∧
      (∀ x y : K, hkCOf (x * y) = hkCMul (hkCOf x) (hkCOf y)) ∧
      ∀ x y : K, (x, y) ≠ hkCOf 0 → ∃ w : K × K, hkCMul (x, y) w = hkCOf 1) ∧
    (∀ a b c : Int, a ≠ 0 →
      ∀ (K : Type) [Lean.Grind.Field K], (∀ n : Int, (Int.cast n : K) = 0 → n = 0) →
        ∀ s : K, s * s = (Int.cast (hkDisc a b c) : K) →
          hkRoot a b c (hkAlpha a b s) ∧ hkRoot a b c (hkBeta a b s) ∧
          (hkDisc a b c ≠ 0 → hkAlpha a b s ≠ hkBeta a b s) ∧
          (∀ k : Int, hkDisc a b c = k * k →
            ∃ p₁ p₂ q : Int, q ≠ 0 ∧ hkAlpha a b s = (Int.cast p₁ : K) / (Int.cast q : K) ∧
              hkBeta a b s = (Int.cast p₂ : K) / (Int.cast q : K))) ∧
    (∀ a b c k : Int, hkDisc a b c = k * k →
      ∀ (K : Type) [Lean.Grind.Field K], ∃ s : K, s * s = (Int.cast (hkDisc a b c) : K)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K inst O hsqrt A B C hA
    exact ⟨fun hD => hk_realK O hsqrt A B C hA hD,
      fun hD => ⟨hk_double_exK O A B C hA hD, fun s hs => hk_doubleK A B C s hs hD⟩,
      fun hD => ⟨fun x => hk_no_rootK O A B C hD x, hk_complexK O hsqrt A B C hA hD⟩⟩
  · intro K inst O
    exact ⟨hk_i_sq, hk_cadd_assoc, hk_cadd_comm, hk_cadd_zero, hk_cadd_neg, hk_cmul_assoc,
      hk_cmul_comm, hk_cmul_one, hk_cmul_add, hk_cone_ne O, hk_cof_add, hk_cof_mul,
      fun x y hz => hk_cinv O x y hz⟩
  · intro a b c ha K inst hchar s hs
    exact ⟨hk_alpha_root a b c ha hchar s hs, hk_beta_root a b c ha hchar s hs,
      fun hD => hk_ne a b c ha hchar s hs hD, fun k hk => hk_rational a b c ha s hs k hk⟩
  · intro a b c k hk K inst
    refine ⟨Int.cast k, ?_⟩
    rw [hk, hk_cast_mul]

## lean
Lean accepts the code.

## challenger
NO OBJECTION. Lean accepts the final code, and `hk_art_113` does not depend on `sorryAx`. Cases (1)–(3) are stated for coefficients in an ordered field with square roots of positive elements, which the supervisor accepted as the model of ℝ. In case (3) the roots `(−B ± i t)/(2A)` exist in `K × K`, whose field laws, inverses and embedding of `K` are proved; there they are unequal and not real, and no root lies in `K`. Case (4) keeps integer coefficients and `D ≠ 0` as the supervisor endorsed, and I can defend no further objection that the prover has not answered.

## critic
1. **The supervisor's explicit instruction for case (3) was not carried out.** The last REVISE asked for `K × K` with `i² = −1` to be built *as a `Lean.Grind.Field`*.
   - The prover declined, saying the class's remaining fields (`nsmul`, `npow`, `zpow`, casts) have names that "vary between core versions". The thread contains no attempt that failed for that reason.
   - Thirteen separate laws are listed instead. Nothing in Lean packages them into a field structure, and `hkCRoot` evaluates the quadratic with ad hoc `hkCAdd`/`hkCMul` terms rather than in a field.
   - So the claim in the doc-comment that `K × K` "is a field extension of `K`" is an informal reading of a list of lemmas, not a stated theorem. It does not satisfy a direction the supervisor gave verbatim.
   - The challenger's acceptance ("even though no instance is registered") waives the requirement rather than answering it.

2. **Cases (1)–(3) may be vacuous, because their hypotheses are never shown to have a model.** Every real-coefficient clause is quantified over a `K` that has a `Lean.Grind.Field`, an `HKOrd K`, and square roots of all positive elements.
   - The file exhibits no such `K`, and core Lean provides none.
   - It also gives no partial check. It does not show, for example, that ℚ admits an `HKOrd` structure, which would at least confirm the ordered-field part is consistent.
   - The supervisor accepted a hypothesis-based treatment of ℝ. That does not cover a statement whose entire content for "real", "equal" and "imaginary" could hold trivially.
   - This is the same undischarged-assumption problem the challenger raised in rounds 2 and 3. It has been moved into the binder but never resolved.

3. **Case (4) is detached from the rest and still departs from the text.**
   - The book's perfect-square case is a refinement of the real case, meaning the roots are real and rational. The code states it in an arbitrary characteristic-zero field with integer coefficients and never links it to the ordered-field setting of cases (1)–(2).
   - "Rational" is rendered only as "equal to `Int.cast p / Int.cast q` in `K`". It is not stated for rational coefficients, even though the defender relied on that reading to justify the integer restriction.
   - "Unequal" holds only under the added hypothesis `D ≠ 0`.
   - Taken together, the final theorem is four loosely related statements whose correspondence to Art. 113 rests on doc-comments rather than on Lean.

The pull request should not merge.

## defender
**1. No `Lean.Grind.Field` instance for `K × K`.** The second conjunct of `hk_art_113` is a Lean statement, not a doc-comment, and it lists the full field axioms for `hkCAdd`/`hkCMul`: associativity, commutativity, both identities, both inverses, distributivity and `1 ≠ 0`. It also proves the embedding of `K`, and `hkCRoot` is evaluated with exactly these operations, so the roots live in a structure that Lean proves is a field. Registering an instance would only bundle these proved laws with bookkeeping fields. The challenger, who raised the issue, judged the content sufficient.

**2. Possible vacuity of cases (1)–(3).** An ordered field in which every positive element has a square root is the standard axiomatization that ℝ satisfies, so the hypotheses have a well-known model and the clauses are not trivial. The supervisor directed in two rounds that the real case stay hypothesis-based "since ℝ cannot be built in core", so demanding an in-core model asks for what the supervisor ruled impossible.

**3. Case (4).**
- **Scope.** The case (4) clause holds in every characteristic-zero field, so it is stronger than a statement tied to the ordered setting and covers ℝ in particular. "Equal to `p/q` with integers `p` and `q ≠ 0`" is the definition of a rational number.
- **Coefficients and `D ≠ 0`.** Clearing denominators multiplies `D` by a nonzero square, so whether `D` is a perfect square is unchanged and integer coefficients lose no generality. `D ≠ 0` is required because `D = 0 = 0²` gives equal roots by the book's own case (2), and the supervisor explicitly ordered "Keep `D ≠ 0` in case (4)".

Lean accepts the code with no `sorryAx`, the challenger has no objection, and the substantive requirements are met, so the pull request should merge.

## supervisor
**MERGE.** Lean accepts the final code with no `sorryAx`. The theorem states Art. 113 faithfully: cases (1)–(3) are stated for coefficients in an ordered field with square roots, which is the hypothesis-based model of ℝ that core Lean forces. In case (3) the roots exist in `K × K`, where every field axiom and the embedding of `K` are proved, so the missing `Lean.Grind.Field` instance is packaging rather than substance. Case (4) keeps integer coefficients and the `D ≠ 0` hypothesis, both justified in the thread, and none of the critic's remaining points holds.
