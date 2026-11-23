## issue
Issue #69. To find the sum of the cubes of the first n natural numbers (Art. 69)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter VI (Harmonical Progression. Theorems connected with the Progressions), Art. 69.
The book prints the following text.
67. The numbers 1, 2, 3,...... are often referred to as the natural numbers; the nth term of the series is n, and the sum of the first n terms is (n/2)(n + 1).
Let the sum be denoted by S; then S = 1^3 + 2^3 + 3^3 + ...... + n^3.
S = n^2 (n + 1)^2 / 4 = {n(n + 1)/2}^2. Thus the sum of the cubes of the first n natural numbers is equal to the square of the sum of these numbers.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_69.

## prover
/-- The sum of the cubes of the first `n` natural numbers:
`sumCubes n = 1^3 + 2^3 + ... + n^3`. -/
def sumCubes : Nat → Nat
  | 0 => 0
  | n + 1 => sumCubes n + (n + 1) ^ 3

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

/-- `n (n + 1)` is even. -/
theorem mul_succ_even (n : Nat) : ∃ j, n * (n + 1) = j + j := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨j + k + 1, ?_⟩
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at hj ⊢
    omega

/-- Hall and Knight, Higher Algebra, Art. 69: the sum of the cubes of the
first `n` natural numbers is `S = 1^3 + 2^3 + ... + n^3 = {n(n + 1)/2}^2`.
That is, it equals the square of the sum of these numbers. -/
theorem hk_art_69 (n : Nat) : sumCubes n = (n * (n + 1) / 2) ^ 2 := by
  obtain ⟨j, hj⟩ := mul_succ_even n
  have h4 := four_mul_sumCubes n
  rw [hj] at h4
  rw [hj, show (j + j) / 2 = j by omega, Nat.pow_two]
  simp only [Nat.add_mul, Nat.mul_add] at h4
  omega

## lean
Lean accepts the code.

## challenger
OBJECTION: The article's stated conclusion is that the sum of the cubes equals the square of the sum of the first n natural numbers. `hk_art_69` only proves the closed form `(n * (n + 1) / 2) ^ 2`. Nowhere is `n * (n + 1) / 2` shown to equal `1 + 2 + ... + n` (for example via a recursive `sumNat` and the identity `sumCubes n = (sumNat n) ^ 2`). So the docstring's claim "it equals the square of the sum of these numbers" is asserted but not proved. Also, truncating `Nat` division makes the closed form faithful only because `n * (n + 1)` is even, and the statement should not rely on a reader checking that unstated fact.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

The prover answered my earlier objection. `sumNat` is now defined recursively as 1 + 2 + ... + n. The theorem `hk_art_69` proves `sumCubes n = (sumNat n) ^ 2`, which is the article's statement that the sum of the cubes is the square of the sum of the numbers.

The second part of the conjunction gives the closed form `(n * (n + 1) / 2) ^ 2`. `two_mul_sumNat` shows that `n * (n + 1) = 2 * sumNat n`, so the truncating `Nat` division is exact and the closed form is faithful.

Both recursive definitions match the prose exactly: `sumCubes` sums the first n cubes starting at 1, `sumNat` sums the first n numbers starting at 1, and n = 0 gives the empty sum. The statement is neither weaker nor stronger than the article. It has no vacuous hypotheses, and Lean accepts the code.

## critic
The final code is correct and faithful to the issue, and the prover fully answered the challenger. The case against merging is weak. These are the strongest points I can make, and none of them shows a mathematical defect.

1. **The exactness of the division is not part of the main theorem's statement.** The second conjunct of `hk_art_69` uses truncating `Nat` division in `(n * (n + 1) / 2) ^ 2`. It is a true equality, but someone reading only the statement still has to know that `n * (n + 1)` is even to see that it means `{n(n+1)/2}^2` and not a floored value. The evenness fact appears only in the docstring and in the separate lemma `two_mul_sumNat`. This was the challenger's second concern. It was addressed in the proof but not in the statement. A statement that did not depend on this would include `2 ∣ n * (n + 1)` or the divisionless form.

2. **The book's displayed form `S = n^2 (n + 1)^2 / 4` is not stated in the form the book gives.** `hk_art_69` gives `(sumNat n)^2` and `(n(n+1)/2)^2`. The divisionless equivalent `4 * S = (n(n+1))^2` exists only as the auxiliary lemma `four_mul_sumCubes`. It is not part of the result that `hk_art_69` exports. This is a presentation gap against the printed text, not an error.

3. **The proofs are fragile to maintain.** Several steps use `omega` on goals containing products of variables. They work only because `simp only [...]` first rewrites the products into shapes that `omega` can treat as matching atoms. A small change in lemma names or simp normal forms could break them. Lean accepts the code now, so this concerns robustness, not correctness.

I cannot honestly claim more than this. The recursive definitions `sumCubes` and `sumNat` match the prose, with the empty sum at `n = 0`. `hk_art_69` proves `sumCubes n = (sumNat n)^2`, which is the article's conclusion that the sum of the cubes is the square of the sum. The closed form is correct, and the earlier objection was answered in substance. My points ask for refinements, not corrections.

## defender
**1. Exactness of the division.** The article's main claim is carried by the first conjunct, `sumCubes n = (sumNat n) ^ 2`, which has no division at all. The second conjunct is a proved equality with the concrete `sumCubes n`, so no floored value can be hiding in it, and `two_mul_sumNat` states the evenness explicitly in the same file.

**2. The displayed form `n^2 (n + 1)^2 / 4`.** The book itself rewrites that form as `{n(n + 1)/2}^2`, which `hk_art_69` states verbatim. The book's intermediate form also appears in division-free shape as the public theorem `four_mul_sumCubes`, which ships in the same file.

**3. Fragility of the proofs.** Lean accepts the code, and the only lemmas it uses are basic core `Nat` lemmas (`Nat.mul_add`, `Nat.add_mul`, `Nat.pow_succ`, and the like). Whether the proofs will survive future toolchain changes is a maintenance question and does not count against faithfulness or correctness, so it gives no reason to block the merge.

The critic concedes that the code is correct and faithful and that these are only requests for refinement. The pull request should merge.

## supervisor
MERGE. Lean accepts the final code, and `hk_art_69` states the article's result faithfully. It proves `sumCubes n = (sumNat n)^2` from recursive definitions that match the prose, and the closed form `(n(n+1)/2)^2` is exact because `two_mul_sumNat` shows the division by 2 leaves no remainder. The critic's three points (where the exactness fact is stated, the divisionless form living in a separate lemma, and proof fragility) are requests for refinement rather than defects, and the defender rebutted each of them.
