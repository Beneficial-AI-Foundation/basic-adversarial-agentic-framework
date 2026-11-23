## issue
Issue #68. To find the sum of the squares of the first n natural numbers (Art. 68)
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter VI (Harmonical Progression. Theorems connected with the Progressions), Art. 68.
The book prints the following text.
67. The numbers 1, 2, 3,...... are often referred to as the natural numbers; the nth term of the series is n, and the sum of the first n terms is (n/2)(n + 1).
Let the sum be denoted by S; then S = 1^2 + 2^2 + 3^2 + ...... + n^2.
S = n(n + 1)(2n + 1)/6.
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_68.

## prover
/-- `sumSq n` is the sum of the squares of the first `n` natural numbers,
`1^2 + 2^2 + ... + n^2`. The empty sum for `n = 0` is `0`. -/
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) ^ 2

/-- Auxiliary form without division: `6 * S = n(n+1)(2n+1)`. -/
theorem sumSq_mul_six (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumSq]
    rw [Nat.mul_add, ih]
    simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Hall and Knight, Higher Algebra, Art. 68: the sum of the squares of the first
`n` natural numbers is `S = 1^2 + 2^2 + ... + n^2 = n(n + 1)(2n + 1)/6`. -/
theorem hk_art_68 (n : Nat) : sumSq n = n * (n + 1) * (2 * n + 1) / 6 := by
  rw [← sumSq_mul_six n, Nat.mul_div_cancel_left _ (by decide)]

## lean
The Lean check failed. Lean rejects the code. <stdin>:15:77: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  f ≥ 0
  e ≥ 0
  d ≥ 0
  c ≥ 0
  c + e - f ≥ 1
  b ≥ 0
  a ≥ 0
  a ≥ 0
where
 a := ↑(sumSq n)
 b := ↑n
 c := ↑n * ↑(n * 2)
 d := ↑n * ↑(n * (n * 2))
 e := ↑n * ↑(n * 4)
 f := ↑n * ↑(n * 6)
'hk_art_68' depends on axioms: [propext, sorryAx]


## challenger
OBJECTION The Lean check failed: in `sumSq_mul_six`, `omega` cannot close the inductive step, so `hk_art_68` depends on `sorryAx` and nothing is proved. After `simp` the goal still contains nonlinear products such as `n * (n * 2)` and `n * (n * 6)`. `omega` treats each product as an unrelated atom, so it cannot derive the identity `6(n+1)^2 + n(n+1)(2n+1) = (n+1)(n+2)(2n+3)`. The step must be proved by a correct normalization, for example by expanding both sides to a canonical polynomial form with `Nat.left_distrib` and `Nat.right_distrib`, or by stating the step as an explicit `calc`. Only after that may `omega` close the linear residue.

## prover
/-- `sumSq n` is the sum of the squares of the first `n` natural numbers,
`1^2 + 2^2 + ... + n^2`. The empty sum for `n = 0` is `0`. -/
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) ^ 2

/-- Auxiliary form without division: `6 * S = n(n+1)(2n+1)`. -/
theorem sumSq_mul_six (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumSq]
    rw [Nat.mul_add, ih]
    simp only [Nat.pow_two, Nat.two_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one,
      Nat.one_mul, Nat.mul_assoc]
    omega

/-- Hall and Knight, Higher Algebra, Art. 68: the sum of the squares of the first
`n` natural numbers is `S = 1^2 + 2^2 + ... + n^2 = n(n + 1)(2n + 1)/6`. -/
theorem hk_art_68 (n : Nat) : sumSq n = n * (n + 1) * (2 * n + 1) / 6 := by
  rw [← sumSq_mul_six n, Nat.mul_div_cancel_left _ (by decide)]

## lean
The Lean check failed. Lean rejects the code. <stdin>:16:4: error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  e ≥ 0
  d ≥ 0
  c ≥ 0
  2*c - e ≤ -1
  b ≥ 0
  a ≥ 0
  a ≥ 0
where
 a := ↑(sumSq n)
 b := ↑n * ↑(n * n)
 c := ↑n * ↑n
 d := ↑n
 e := ↑n * ↑(n * 2)
'hk_art_68' depends on axioms: [propext, sorryAx]


## challenger
OBJECTION The Lean check failed again: `omega` cannot close the inductive step of `sumSq_mul_six`, so `hk_art_68` still depends on `sorryAx` and nothing is proved. The `simp only` set leaves the atoms `n * n` and `n * (n * 2)` unrelated. `omega` therefore cannot use the needed fact `n * (n * 2) = 2 * (n * n)`, and the leftover constraint `2*c - e ≤ -1` is consistent. Rewrite every inner factor of the form `n * 2` with `Nat.mul_two` (giving `n + n`), and distribute it again so that only the monomials `n`, `n * n` and `n * (n * n)` remain. Alternatively, prove the step with an explicit `calc` before calling `omega`.

## prover
/-- `sumSq n` is the sum of the squares of the first `n` natural numbers,
`1^2 + 2^2 + ... + n^2`. The empty sum for `n = 0` is `0`. -/
def sumSq : Nat → Nat
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) ^ 2

/-- Expansion of `x(x+1)(2x+1)` into the monomials `x*x*x`, `x*x` and `x`. -/
theorem hk_poly (x : Nat) :
    x * (x + 1) * (2 * x + 1) = 2 * (x * x * x) + 3 * (x * x) + x := by
  have h1 : x * (x + 1) = x * x + x := by rw [Nat.mul_add, Nat.mul_one]
  have h2 : (x * x + x) * (2 * x + 1) = (x * x + x) * (2 * x) + (x * x + x) := by
    rw [Nat.mul_add, Nat.mul_one]
  have h3 : (x * x + x) * (2 * x) = 2 * ((x * x + x) * x) := Nat.mul_left_comm _ _ _
  have h4 : (x * x + x) * x = x * x * x + x * x := Nat.add_mul _ _ _
  rw [h1, h2, h3, h4]
  omega

/-- Expansion of `(x+1)(x+1)`. -/
theorem hk_sq_succ (x : Nat) : (x + 1) * (x + 1) = x * x + 2 * x + 1 := by
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

/-- Expansion of `(x+1)(x+1)(x+1)`. -/
theorem hk_cube_succ (x : Nat) :
    (x + 1) * (x + 1) * (x + 1) = x * x * x + 3 * (x * x) + 3 * x + 1 := by
  have c1 : (x + 1) * (x + 1) * (x + 1) = (x + 1) * (x + 1) * x + (x + 1) * (x + 1) := by
    rw [Nat.mul_add ((x + 1) * (x + 1)) x 1, Nat.mul_one]
  have c2 : (x + 1) * (x + 1) * x = (x * x + 2 * x + 1) * x := by
    rw [hk_sq_succ x]
  have c3 : (x * x + 2 * x + 1) * x = x * x * x + 2 * (x * x) + x := by
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.mul_assoc 2 x x]
  have c4 := hk_sq_succ x
  omega

/-- Auxiliary form without division: `6 * S = n(n+1)(2n+1)`. -/
theorem sumSq_mul_six (n : Nat) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show 6 * (sumSq n + (n + 1) ^ 2) = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1)
    have h1 := hk_poly n
    have h2 := hk_poly (n + 1)
    have h3 := hk_sq_succ n
    have h4 := hk_cube_succ n
    have h5 : (n + 1) ^ 2 = (n + 1) * (n + 1) := Nat.pow_two _
    omega

/-- Hall and Knight, Higher Algebra, Art. 68: the sum of the squares of the first
`n` natural numbers is `S = 1^2 + 2^2 + ... + n^2 = n(n + 1)(2n + 1)/6`. -/
theorem hk_art_68 (n : Nat) : sumSq n = n * (n + 1) * (2 * n + 1) / 6 := by
  rw [← sumSq_mul_six n, Nat.mul_div_cancel_left _ (by decide)]

## lean
Lean accepts the code.

## challenger
NO OBJECTION

Lean now accepts the code, so `hk_art_68` no longer depends on `sorryAx`. The recursive `sumSq` faithfully encodes `1^2 + 2^2 + ... + n^2`, with the empty sum `0` for `n = 0`. The statement matches the book's formula `S = n(n + 1)(2n + 1)/6`. The truncating division is exact, because `sumSq_mul_six` proves `6 * S = n(n + 1)(2n + 1)` in the same file.

## critic
**Critic: I oppose the merge.** The best case I can make is below. It is a weak case. Lean accepts the code, and the main statement is correct. My objections concern how the result is stated and packaged, not whether it is true.

1. **The main theorem hides the book's exactness claim behind truncating division.**
   - The book's formula `S = n(n+1)(2n+1)/6` says two things: 6 divides the product, and the quotient is S.
   - `hk_art_68` uses `Nat` `/`, which is floor division. On its own, the theorem is the weaker-looking claim `sumSq n = ⌊n(n+1)(2n+1)/6⌋`. It does not assert divisibility.
   - The exact content lives only in the auxiliary lemma `sumSq_mul_six`. The challenger's acceptance relies on reading the two theorems together, but the issue names `hk_art_68` as the main theorem.
   - A faithful main statement would state divisibility as well, for example `6 ∣ n*(n+1)*(2*n+1) ∧ sumSq n = …`. Alternatively it would put `6 * sumSq n = …` in the named theorem itself.
   - In fairness, `Nat.mul_div_cancel_left` and `sumSq_mul_six` together make the division exact. So this is a weakness in presentation, not an error.

2. **The sum is an ad hoc recursion that nothing ties to a standard sum.**
   - `sumSq` is a private recursive definition. Its fidelity to `1² + 2² + … + n²` rests on reading two equations and the docstring.
   - No lemma connects it to a core-library form of the sum, such as `((List.range n).map (fun i => (i+1)^2)).sum`.
   - The recursion is plainly correct, so this is a modest concern. Still, a reviewer must trust the definition rather than a checked link to the book's series.
   - The `n = 0` case is a harmless generalisation. The book means n ≥ 1.

3. **Packaging and the prover's response to the challenger.**
   - The prover did answer the challenger's objection, though not by the suggested route. The challenger asked for `Nat.mul_two` rewriting or a `calc`. The prover instead added four global helper lemmas and handed `omega` linear facts about fixed product atoms. That is a valid answer to "omega sees nonlinear atoms", and Lean confirms it works.
   - However, the file now adds generic top-level names (`sumSq`, `hk_poly`, `hk_sq_succ`, `hk_cube_succ`, `sumSq_mul_six`) with no namespace. These risk clashing with other articles in the same project.
   - The helper lemmas restate routine ring facts by hand. That makes the proof brittle and verbose for a one-line identity.

**Overall:** none of these points shows the theorem is wrong or the proof unsound. My strongest objection is point 1, that the named theorem does not on its own carry the divisibility claim implicit in the book's formula.

## defender
**Defender: the pull request should merge.**

1. `hk_art_68` states the book's formula `S = n(n+1)(2n+1)/6` exactly as printed, and the same file proves `6 * sumSq n = n*(n+1)*(2*n+1)` in `sumSq_mul_six`, so divisibility follows immediately (`⟨sumSq n, (sumSq_mul_six n).symm⟩`) and the division is certified exact. The issue requires only that the main theorem carry the name `hk_art_68`, not that every supporting fact be packed into it, so the article's full content is machine-checked here.

2. `sumSq` is the standard recursive definition of a finite sum. `List.sum` in core is itself defined by the same kind of recursion, so linking the two would only replace one two-line definition with another. The two equations `sumSq 0 = 0` and `sumSq (n+1) = sumSq n + (n+1)^2` match `1² + … + n²` directly, and the `n = 0` case is, as you concede, a harmless generalisation.

3. Without Mathlib there is no `ring` tactic, so hand-proved expansion lemmas are the normal core-only way to give `omega` linear facts, and Lean has confirmed they work. Any name clash with another article would show up as a compile error when the files are combined, and adding a namespace is a trivial follow-up that does not affect whether this correct, sorry-free proof should merge.

## supervisor
**REVISE**

Lean accepts the code and the formula is correct. However, the critic's first point stands: with truncating `Nat` division, `hk_art_68` on its own only says `sumSq n = ⌊n(n+1)(2n+1)/6⌋`, which is weaker than the book's exact claim, and the exact content sits only in an auxiliary lemma. Restate `hk_art_68` to carry exactness itself, either as `6 * sumSq n = n * (n + 1) * (2 * n + 1)` or as the conjunction `6 ∣ n * (n + 1) * (2 * n + 1) ∧ sumSq n = n * (n + 1) * (2 * n + 1) / 6`, and put the helper lemmas in a namespace such as `HK68` to avoid name clashes.

## prover
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

## lean
Lean accepts the code.

## challenger
NO OBJECTION

Lean accepts the revised code. `hk_art_68` now states the divisibility `6 ∣ n * (n + 1) * (2 * n + 1)` together with `HK68.sumSq n = n * (n + 1) * (2 * n + 1) / 6`, so the named theorem by itself says the division is exact, as the book's formula does. `HK68.sumSq` correctly encodes `1^2 + 2^2 + ... + n^2`, and the helper lemmas now sit in the `HK68` namespace, which answers both points of the supervisor's REVISE.

## critic
**Critic: I oppose the merge.** The case is weak. Lean accepts the final code. The prover answered every objection: the challenger's `omega` failures and both points of the supervisor's REVISE (exactness in `hk_art_68`, and the `HK68` namespace). What remains are concerns of fidelity and style, not of correctness.

1. **The series itself is never checked against the book's sum.**
   - The book's S is the series `1² + 2² + … + n²`.
   - The code replaces it with the private recursion `HK68.sumSq`, and its meaning rests on two equations and a docstring.
   - No lemma links it to a core form such as `((List.range n).map (fun i => (i+1)^2)).sum`.
   - So the reviewer must trust the definition rather than a checked statement about the series the article names.
   - The defender's reply that `List.sum` is "the same kind of recursion" admits the link would be easy, yet it was not given.

2. **The named theorem still leads with truncating division and adds a redundant conjunct.**
   - The conjunct `6 ∣ …` is obtained directly from `sumSq_mul_six` and only re-exports it.
   - The cleanest faithful statement of "S = n(n+1)(2n+1)/6, exactly" is the division-free equation `6 * S = n(n+1)(2n+1)`. That equation is still only an auxiliary lemma, not the main theorem.
   - The current form is correct and does carry exactness. Its second conjunct read alone, however, is still the floor statement.

3. **The proof is brittle and does not reflect the article's method.**
   - Art. 68 derives the formula by summing `n³ − (n−1)³ = 3n² − 3n + 1`. The proof instead hand-expands polynomials into fixed product atoms.
   - It then relies on `omega` matching syntactically identical nonlinear terms, such as `(n+1)*(n+1+1)` under `show`.
   - Any change in how Lean normalises these terms could break it.
   - The issue only asks for "state and prove", so this is not disqualifying.

**Overall:** none of these points shows the theorem wrong or the proof unsound. My strongest point is point 1, the missing check that `sumSq` is the book's series.

## defender
**Defender: the pull request should merge.**

1. **The series.** The equations `sumSq 0 = 0` and `sumSq (n+1) = sumSq n + (n+1)^2` are the standard inductive definition of `1² + 2² + … + n²`, so they are no less trustworthy than `List.sum`, which is itself a recursive definition that would also need trusting. Neither the challenger nor the supervisor objected to this definition, and adding a link to `List.range` would only relate two equivalent definitions without adding mathematical content.

2. **The statement.** The supervisor's REVISE listed this exact conjunction as an acceptable form, and the `6 ∣ …` conjunct is not redundant: it is what makes the named theorem assert exactness on its own, which was your own strongest objection last round. Read as a whole, `hk_art_68` says "6 divides the product and the quotient is S", which is the book's printed formula, and the division-free equation is also proved in the same file as `HK68.sumSq_mul_six`.

3. **The proof method.** The issue asks only to state and prove the result, not to reproduce the book's telescoping argument, and without Mathlib's `ring` the hand-proved expansions are the normal core-only route. The `show` goal is fixed and Lean checks it by definitional unfolding, so a hypothetical future change to Lean is not grounds to block a proof that Lean accepts today with no `sorry`.

## supervisor
**MERGE.** Lean accepts the final code. `hk_art_68` states that 6 divides n(n+1)(2n+1) and that `HK68.sumSq n` equals the quotient, which is the book's exact formula, and `HK68.sumSq` plainly encodes 1² + 2² + … + n². The critic's remaining points do not show the statement unfaithful or the proof unsound: the missing link to `List.sum`, the divisibility conjunct, and the proof method all concern style.
