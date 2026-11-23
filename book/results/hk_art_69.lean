/-- The sum of the cubes of the first `n` natural numbers:
`sumCubes n = 1^3 + 2^3 + ... + n^3`. -/
def sumCubes : Nat → Nat
  | 0 => 0
  | n + 1 => sumCubes n + (n + 1) ^ 3

/-- The sum of the first `n` natural numbers:
`sumNat n = 1 + 2 + ... + n`. -/
def sumNat : Nat → Nat
  | 0 => 0
  | n + 1 => sumNat n + (n + 1)

/-- Art. 67 without division: `2 * (1 + 2 + ... + n) = n (n + 1)`.
In particular `n (n + 1)` is even, so the division below is exact. -/
theorem two_mul_sumNat (n : Nat) : 2 * sumNat n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * (sumNat k + (k + 1)) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- Art. 67: the sum of the first `n` natural numbers is `n (n + 1) / 2`. -/
theorem sumNat_eq (n : Nat) : sumNat n = n * (n + 1) / 2 := by
  have h := two_mul_sumNat n
  omega

/-- Auxiliary form without division: `4 * S = (n (n + 1))^2`. -/
theorem four_mul_sumCubes (n : Nat) :
    4 * sumCubes n = (n * (n + 1)) * (n * (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 4 * (sumCubes k + (k + 1) ^ 3)
        = ((k + 1) * (k + 1 + 1)) * ((k + 1) * (k + 1 + 1))
    rw [Nat.mul_add, ih]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_one,
      Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega

/-- Hall and Knight, Higher Algebra, Art. 69: the sum of the cubes of the
first `n` natural numbers equals the square of the sum of these numbers,
`1^3 + 2^3 + ... + n^3 = (1 + 2 + ... + n)^2`, and in closed form
`S = {n(n + 1)/2}^2`. The division is exact since `2 * sumNat n = n (n + 1)`
(see `two_mul_sumNat`). -/
theorem hk_art_69 (n : Nat) :
    sumCubes n = (sumNat n) ^ 2 ∧ sumCubes n = (n * (n + 1) / 2) ^ 2 := by
  have hsq : sumCubes n = (sumNat n) ^ 2 := by
    have h1 := four_mul_sumCubes n
    rw [← two_mul_sumNat, Nat.mul_mul_mul_comm 2 (sumNat n) 2 (sumNat n)] at h1
    rw [Nat.pow_two]
    omega
  refine ⟨hsq, ?_⟩
  rw [← sumNat_eq]
  exact hsq
