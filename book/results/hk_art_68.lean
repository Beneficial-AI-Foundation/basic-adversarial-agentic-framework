/-- `HK68.sumSq n` is the sum of the squares of the first `n` natural numbers,
`1^2 + 2^2 + ... + n^2`. The empty sum for `n = 0` is `0`. -/
def HK68.sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => HK68.sumSq n + (n + 1) ^ 2

namespace HK68

/-- Expansion of `x(x+1)(2x+1)` into the monomials `x*x*x`, `x*x` and `x`. -/
theorem poly (x : Nat) :
    x * (x + 1) * (2 * x + 1) = 2 * (x * x * x) + 3 * (x * x) + x := by
  have h1 : x * (x + 1) = x * x + x := by rw [Nat.mul_add, Nat.mul_one]
  have h2 : (x * x + x) * (2 * x + 1) = (x * x + x) * (2 * x) + (x * x + x) := by
    rw [Nat.mul_add, Nat.mul_one]
  have h3 : (x * x + x) * (2 * x) = 2 * ((x * x + x) * x) := Nat.mul_left_comm _ _ _
  have h4 : (x * x + x) * x = x * x * x + x * x := Nat.add_mul _ _ _
  rw [h1, h2, h3, h4]
  omega

/-- Expansion of `(x+1)(x+1)`. -/
theorem sq_succ (x : Nat) : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- Expansion of `(x+1)(x+1)(x+1)`. -/
theorem cube_succ (x : Nat) :
    (x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * (x * x) + 3 * x + 1 := by
  have c1 : (x + 1) * (x + 1) * (x + 1) = (x + 1) * (x + 1) * x + (x + 1) * (x + 1) := by
    rw [Nat.mul_add ((x + 1) * (x + 1)) x 1, Nat.mul_one]
  have c2 : (x + 1) * (x + 1) * x = (x * x + 2 * x + 1) * x := by
    rw [sq_succ x]
  have c3 : (x * x + 2 * x + 1) * x = x * x * x + 2 * (x * x) + x := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc 2 x x]
  have c4 := sq_succ x
  omega

/-- Form without division: `6 * S = n(n+1)(2n+1)`. -/
theorem sumSq_mul_six (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 6 * (sumSq n + (n + 1) ^ 2) = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
    have h1 := poly n
    have h2 := poly (n + 1)
    have h3 := sq_succ n
    have h4 := cube_succ n
    have h5 : (n + 1) ^ 2 = (n + 1) * (n + 1) := Nat.pow_two _
    omega

end HK68

/-- Hall and Knight, Higher Algebra, Art. 68: the sum of the squares of the first
`n` natural numbers is `S = 1^2 + 2^2 + ... + n^2 = n(n + 1)(2n + 1)/6`.
The division is exact: `6` divides `n(n + 1)(2n + 1)`, and the quotient is `S`. -/
theorem hk_art_68 (n : Nat) :
    6 ∣ n * (n + 1) * (2 * n + 1) ∧
      HK68.sumSq n = n * (n + 1) * (2 * n + 1) / 6 := by
  refine ⟨⟨HK68.sumSq n, (HK68.sumSq_mul_six n).symm⟩, ?_⟩
  rw [← HK68.sumSq_mul_six n, Nat.mul_div_cancel_left _ (by decide)]
