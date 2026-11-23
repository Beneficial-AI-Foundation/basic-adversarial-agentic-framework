## issue
Issue #114. Art. 114, The Theory of Quadratic Equations
Source: H. S. Hall and S. R. Knight, Higher Algebra, Fourth Edition, 1891, Chapter IX (The Theory of Quadratic Equations), Art. 114.
The book prints the following text.
111. After suitable reduction every quadratic equation may be written in the form ax^2 + bx + c = 0 ......(1), and the solution of the equation is x = (−b ± √(b^2 − 4ac))/(2a) ......(2).
Since α = (−b + √(b^2 − 4ac))/(2a), β = (−b − √(b^2 − 4ac))/(2a),
we have by addition α + β = (−b + √(b^2 − 4ac) − b − √(b^2 − 4ac))/(2a) = −2b/(2a) = −b/a ......(1); and by multiplication we have αβ = (−b + √(b^2 − 4ac))(−b − √(b^2 − 4ac))/(4a^2) = ((−b)^2 − (b^2 − 4ac))/(4a^2) = 4ac/(4a^2) = c/a ......(2).
State the result of this article as a Lean theorem and prove it.
The main theorem of the code must have the name hk_art_114.

## prover
/-- Hall & Knight, *Higher Algebra*, Art. 114 (relations between roots and coefficients).

Let `a x^2 + b x + c = 0` be a quadratic equation with `a ≠ 0`. Let `s` be a square root of
the discriminant, so `s * s = b^2 - 4ac`. The two roots are
`α = (-b + s) / (2a)` and `β = (-b - s) / (2a)`. Then

* `α + β = -b / a`, and
* `α * β = c / a`.

The statement is made over an arbitrary field `K` from the core `Lean.Grind.Field` class.
We assume `2 ≠ 0` in `K`, as the root formula itself requires. -/
theorem hk_art_114 {K : Type} [Lean.Grind.Field K] (a b c s : K)
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s * s = b ^ 2 - 4 * a * c) :
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
  constructor <;> grind

## lean
Lean accepts the code.

## challenger
OBJECTION The article's result concerns the roots of the equation ax² + bx + c = 0, but the theorem never links α and β to that equation. It never proves, or even states, that (-b ± s)/(2a) satisfy a·x² + b·x + c = 0, or that these are the two roots. As written, it is only an identity about two formal expressions built from an arbitrary s with s·s = b² − 4ac. To match the prose "α and β are the roots of (1)", the statement should either add the conclusion that α and β are roots, or take as hypotheses that α and β are the roots (for example a·x² + b·x + c = a(x − α)(x − β)) and derive α + β = −b/a and αβ = c/a from that.

## prover
The objection holds, so the statement is repaired. The theorem now also proves that `α` and `β` satisfy `a x² + b x + c = 0`. It also proves that `a x² + b x + c` factors as `a (x - α)(x - β)` for every `x`, which makes them the two roots. I have not run the revised code through the checker, so whether `grind` closes the three new goals is untested.

```lean
-- Answer to the challenger: the objection is accepted and the statement is repaired.
-- The theorem now also proves that α and β satisfy the equation a x^2 + b x + c = 0.
-- It also proves that a x^2 + b x + c = a (x - α)(x - β) for every x, so α and β are
-- the two roots of (1). The relations α + β = -b/a and αβ = c/a are the claim of the article.

/-- Hall & Knight, *Higher Algebra*, Art. 114 (relations between roots and coefficients).

Let `a x^2 + b x + c = 0` be a quadratic equation with `a ≠ 0`. Let `s` be a square root of
the discriminant, so `s * s = b^2 - 4ac`. Put `α = (-b + s) / (2a)` and `β = (-b - s) / (2a)`. Then

* `α` and `β` are roots of the equation: `a α^2 + b α + c = 0` and `a β^2 + b β + c = 0`;
* they are the two roots: `a x^2 + b x + c = a (x - α) (x - β)` for every `x`;
* `α + β = -b / a`, and
* `α * β = c / a`.

The statement is made over an arbitrary field `K` from the core `Lean.Grind.Field` class.
We assume `2 ≠ 0` in `K`, as the root formula itself requires. -/
theorem hk_art_114 {K : Type} [Lean.Grind.Field K] (a b c s : K)
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s * s = b ^ 2 - 4 * a * c) :
    a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 ∧
    a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 ∧
    (∀ x : K, a * x ^ 2 + b * x + c
        = a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a))) ∧
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro x
    grind
  · grind
  · grind
```

## lean
The Lean check failed. Lean rejects the code. <stdin>:1:0: error: unexpected identifier; expected command
<stdin>:1:83: error: unexpected token; expected ':'
<stdin>:36:0: error: unexpected token '`'; expected command
'hk_art_114' depends on axioms: [propext, Classical.choice, Quot.sound]


## challenger
OBJECTION The Lean check failed, so the revision is rejected as submitted. The errors at 1:0 and 36:0 show that the prose paragraph and the closing code fence were passed to Lean as part of the file. Lean does print an axiom report for `hk_art_114`, but that does not count as acceptance while the file itself fails to parse. The prover must resubmit exactly the Lean source and get a clean pass, which would also settle their own admission that the new `grind` goals, including the `∀ x` factorization, are untested.

## prover
-- Answer to the challenger: the failure was in the format of the submission, not in the proof.
-- The previous reply put a prose paragraph and a Markdown fence around the code, and Lean tried
-- to parse them as commands. This reply is only the Lean source.
-- The checker still elaborated `hk_art_114` and printed its axiom report. That suggests the
-- five `grind` goals closed, including the `∀ x` factorization. A clean pass on this file is
-- what will confirm it.
-- The earlier objection about linking α and β to the equation still stands as answered. The
-- theorem proves that α and β satisfy a x^2 + b x + c = 0. It also proves that
-- a x^2 + b x + c = a (x - α)(x - β) for every x, so they are the two roots.

/-- Hall & Knight, *Higher Algebra*, Art. 114 (relations between roots and coefficients).

Let `a x^2 + b x + c = 0` be a quadratic equation with `a ≠ 0`. Let `s` be a square root of
the discriminant, so `s * s = b^2 - 4ac`. Put `α = (-b + s) / (2a)` and `β = (-b - s) / (2a)`. Then

* `α` and `β` are roots of the equation: `a α^2 + b α + c = 0` and `a β^2 + b β + c = 0`;
* they are the two roots: `a x^2 + b x + c = a (x - α) (x - β)` for every `x`;
* `α + β = -b / a`, and
* `α * β = c / a`.

The statement is made over an arbitrary field `K` from the core `Lean.Grind.Field` class.
We assume `2 ≠ 0` in `K`, as the root formula itself requires. -/
theorem hk_art_114 {K : Type} [Lean.Grind.Field K] (a b c s : K)
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s * s = b ^ 2 - 4 * a * c) :
    a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 ∧
    a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 ∧
    (∀ x : K, a * x ^ 2 + b * x + c
        = a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a))) ∧
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro x
    grind
  · grind
  · grind

## lean
Lean accepts the code.

## challenger
NO OBJECTION

## critic
**Case against merging #114**

1. **The theorem states the result for the formula expressions, not for the roots.** The article's content is a relation between *the roots* and the coefficients. The final theorem defines α and β by the quadratic formula. It then proves that they satisfy the equation and that a·x² + b·x + c = a(x − α)(x − β). It never states the direct converse: if r is a root, then r = α or r = β. That follows from the factorization in a field with a ≠ 0, but it is left implicit. The challenger offered a second option: take α, β as given roots, for example by a factorization hypothesis, and derive α + β = −b/a and αβ = c/a. The prover did not take it. So someone holding two arbitrary roots cannot apply `hk_art_114` directly. They must first show that their roots coincide with the formula expressions for some square root s. The fix answers the letter of the first objection but only half of its suggested remedy.

2. **The prover's answer to the second objection rested on a wrong inference.** The prover argued that the axiom report printed despite the parse errors "suggests the five `grind` goals closed." The challenger had already said that a report from a failing file does not count as acceptance. The repair is supported only because the final run passed. It is not supported by the prover's argument. The prover had earlier admitted the new goals were "untested," and the clean pass is the only evidence that `grind` closes them, including the `∀ x` factorization. The challenger's "NO OBJECTION" accepts that pass, so this is a weakness in the reasoning, not a defect in the code.

3. **The file is not in mergeable form and the proof shows nothing of the article's argument.** The submitted source opens with conversational review comments ("Answer to the challenger: the failure was in the format…"). These belong to the thread, not the repository. Each of the five goals is closed by a bare `grind`, with no trace of the book's derivation by addition and multiplication. That derivation is the content of the article. The issue only says "prove it," so this is a quality objection rather than a correctness one. Separately, the issue's header says Art. 114, but the quoted text is numbered 111. Nobody checked which article the theorem actually formalizes.

The kernel accepts the final code, and the statement is mathematically sound. The case against merging rests on how faithfully it captures the article's "roots" framing (point 1) and on the file's hygiene (point 3), not on correctness.

## defender
**Point 1.** The article itself defines α and β by the formula ("Since α = (−b + √…)/(2a), β = …"), so the theorem states exactly the book's claim. The challenger offered its two remedies as alternatives ("either … or"), and the prover took the first; the proved factorization a·x² + b·x + c = a(x − α)(x − β) gives the converse in any field with a ≠ 0, which the challenger accepted with "NO OBJECTION".

**Point 2.** The repository merges code, not the thread's reasoning, and the final file passed the checker cleanly. That pass closes all five `grind` goals, including the `∀ x` factorization; the critic itself concedes this is "not a defect in the code".

**Point 3.** I concede that the leading `--` review comments are thread chatter and should be removed before merge, but they are inert to Lean and cost a one-line cleanup, not a rejection. The issue asks only to "state … and prove it", so a `grind` proof is correct. The "111" label covers only the quoted setup of the quadratic formula, while the conclusions α + β = −b/a and αβ = c/a are exactly the relations of Art. 114 that the theorem formalizes.

## supervisor
REVISE. Lean accepts the final code, and its statement faithfully captures the article: the book itself defines α and β by the root formula, and the proved factorization a·x² + b·x + c = a(x − α)(x − β) settles the "roots" framing. However, the critic's hygiene point stands and the defender concedes it: delete the leading `--` "Answer to the challenger…" comments so the file holds only the docstring and theorem, then rerun the checker and resubmit.

## prover
/-- Hall & Knight, *Higher Algebra*, Art. 114 (relations between roots and coefficients).

Let `a x^2 + b x + c = 0` be a quadratic equation with `a ≠ 0`. Let `s` be a square root of
the discriminant, so `s * s = b^2 - 4ac`. Put `α = (-b + s) / (2a)` and `β = (-b - s) / (2a)`. Then

* `α` and `β` are roots of the equation: `a α^2 + b α + c = 0` and `a β^2 + b β + c = 0`;
* they are the two roots: `a x^2 + b x + c = a (x - α) (x - β)` for every `x`;
* `α + β = -b / a`, and
* `α * β = c / a`.

The statement is made over an arbitrary field `K` from the core `Lean.Grind.Field` class.
We assume `2 ≠ 0` in `K`, as the root formula itself requires. -/
theorem hk_art_114 {K : Type} [Lean.Grind.Field K] (a b c s : K)
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) (hs : s * s = b ^ 2 - 4 * a * c) :
    a * ((-b + s) / (2 * a)) ^ 2 + b * ((-b + s) / (2 * a)) + c = 0 ∧
    a * ((-b - s) / (2 * a)) ^ 2 + b * ((-b - s) / (2 * a)) + c = 0 ∧
    (∀ x : K, a * x ^ 2 + b * x + c
        = a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a))) ∧
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    ((-b + s) / (2 * a)) * ((-b - s) / (2 * a)) = c / a := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro x
    grind
  · grind
  · grind

## lean
Lean accepts the code.

## challenger
NO OBJECTION

## critic
**Case against merging #114**

1. **The theorem is not stated for the roots of the equation.** The article's result is that the two roots of ax² + bx + c = 0 satisfy α + β = −b/a and αβ = c/a. The final `hk_art_114` proves this only for the formula expressions (−b ± s)/(2a), and only when some `s` with `s * s = b² − 4ac` exists in `K`.
   - Someone holding two roots r₁, r₂ cannot apply the theorem directly. They must first build `s`, for example s = a(r₁ − r₂), and show their roots match the formula.
   - The direct converse ("every root equals α or β") is never stated. It follows from the factorization only through an extra step that is not written down.
   - The challenger offered a second remedy: take the roots as hypotheses and derive the relations. That remedy would have captured the article's claim directly, and the prover did not take it.

   The challenger's "NO OBJECTION" accepts the weaker form, but it does not make that form the article's statement.

2. **The supporting argument for the repair was unsound, and the new conjuncts go beyond the article.** The prover claimed that the axiom report from the file that failed to parse "suggests the five `grind` goals closed." That is not evidence. Only the later clean runs show the repair works. The repair also changed the theorem's scope. The book's result in this article is only the sum and product relations. The theorem now also asserts root membership and the factorization. These additions answer the challenger, but they move the stated result away from the article being formalized.

3. **The proof and the provenance are not reviewable against the source.** All five goals are closed by a bare `grind`. Nothing in the proof follows the book's derivation by addition and multiplication, which is what the article contains.
   - The issue headed "Art. 114" quotes text numbered 111.
   - The defender's claim that "111" covers only the setup was never checked against the book.
   - The docstring asserts "Art. 114" without anyone confirming that this is the article being formalized.

**Concessions.** The final file contains only the docstring and the theorem, as the supervisor required, and Lean accepts it. The statement is mathematically correct. The prover did answer every challenger objection, and the challenger raised no further objection. My case therefore rests on how faithfully the theorem captures the article (point 1), on scope (point 2), and on unverified provenance (point 3), not on correctness.

## defender
**Point 1.** The article itself defines α and β by the root formula and assumes √(b² − 4ac), so a theorem about (−b ± s)/(2a) with s·s = b² − 4ac is the book's own claim. The proved factorization a·x² + b·x + c = a(x − α)(x − β), with a ≠ 0 in a field, already yields "every root is α or β" by the zero-product property; the challenger offered its two remedies as alternatives and accepted this one, and the supervisor ruled that it settles the "roots" framing.

**Point 2.** The repository merges code, not the thread's reasoning, and two clean checker runs confirm that all five `grind` goals close, which the critic itself concedes. The added conjuncts were requested by the challenger to tie α and β to equation (1), and they leave the article's sum and product relations intact. The critic cannot fault the theorem in point 1 for being too weak to reach the roots and then fault it here for asserting that they are the roots.

**Point 3.** The issue asks only to "state … and prove it," so a kernel-checked `grind` proof meets the requirement, and the issue does not ask the proof to reproduce the derivation. The docstring's "Art. 114" and the mandated name `hk_art_114` come straight from the issue header. The theorem formalizes exactly the conclusions in the quoted text, α + β = −b/a and αβ = c/a, so the "111" label within that quote does not change what is proved.

## supervisor
**MERGE.** Lean accepts the final file, which now holds only the docstring and theorem. Its statement matches the article: the book defines α and β by the root formula, and the theorem proves α + β = −b/a and αβ = c/a for those roots, with the factorization tying them to equation (1). The critic's remaining points do not stand: the added conjuncts only reinforce the "roots" framing, the issue does not require the proof to follow the book's derivation, and the theorem formalizes exactly the quoted conclusions whatever the article number.
