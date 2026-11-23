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
