import Adversarial.PullRequest

/-! The example issues. Each one is prose with mathematics, with the name of
the Lean theorem that a pull request must prove. Two of the claims are false,
so a correct flow ends them with a rejection. -/

namespace Adversarial.Examples

/-- A short true claim, which a first attempt usually proves. -/
def evenIssue : Issue where
  number := 12
  title := "The sum of two even numbers is even"
  text := "A natural number n is even when n = 2k for some natural number k. " ++
    "Prove that the sum of two even natural numbers is even."
  theoremName := "even_add_even"

/-- A false claim, since 0 + 1 ≠ 0. -/
def successorIssue : Issue where
  number := 15
  title := "Every natural number equals its successor"
  text := "Prove that n + 1 = n for every natural number n."
  theoremName := "succ_fixed"

/-- A harder issue. The prose speaks of rational numbers, and the Lean core
library has no ready proof of the claim. The agents must agree on a statement
and find a proof without Mathlib. -/
def rationalIssue : Issue where
  number := 21
  title := "No rational number has square 2"
  text := "Prove that there is no rational number r with r² = 2."
  theoremName := "no_rational_sqrt_two"

/-- A harder issue with a long proof. The agents must define primality and
prove the claim without Mathlib. -/
def primesIssue : Issue where
  number := 22
  title := "There are infinitely many primes"
  text := "A natural number p is prime when p ≥ 2 and its only divisors are 1 and p. " ++
    "Prove that for every natural number n there is a prime p with p > n."
  theoremName := "exists_prime_gt"

/-- An issue whose claim is false, since 40² + 40 + 41 = 41². -/
def polynomialIssue : Issue where
  number := 23
  title := "A polynomial with prime values"
  text := "Prove that n² + n + 41 is a prime number for every natural number n."
  theoremName := "euler_polynomial_prime"

/-- An issue in informal language. The agents must choose a formal model of
people and of acquaintance, and the proof needs a case analysis that Lean
cannot find by itself. The claim is the Ramsey bound R(3, 3) ≤ 6. -/
def partyIssue : Issue where
  number := 24
  title := "Three friends or three strangers"
  text := "Prove that among any six people there are three who all know one another, " ++
    "or three no two of whom know each other."
  theoremName := "party_of_six"

/-- An issue with a long proof. The uniqueness part needs Euclid's lemma and
a statement about lists of primes up to order. -/
def factorizationIssue : Issue where
  number := 25
  title := "Unique factorization into primes"
  text := "A natural number p is prime when p ≥ 2 and its only divisors are 1 and p. " ++
    "Prove that every natural number n ≥ 2 is a product of primes, and that this " ++
    "product is unique up to the order of the factors."
  theoremName := "unique_factorization"

/-- An issue about congruences, with a proof that needs induction and the
binomial expansion or a counting argument. -/
def fermatIssue : Issue where
  number := 26
  title := "Fermat's little theorem"
  text := "Let p be a prime number and let a be an integer that p does not divide. " ++
    "Prove that a^(p−1) ≡ 1 (mod p)."
  theoremName := "fermat_little"

/-- An issue about real numbers. The Lean core library has no type of real
numbers, so the agents must agree on what a faithful statement is. -/
def realIssue : Issue where
  number := 27
  title := "An inequality of real numbers"
  text := "Prove that x² + y² ≥ 2xy for all real numbers x and y, with equality " ++
    "exactly when x = y."
  theoremName := "sum_of_squares_ge"

/-- An issue about finite sets, stated with boxes and objects. -/
def pigeonholeIssue : Issue where
  number := 28
  title := "The pigeonhole principle"
  text := "Prove that when n + 1 objects lie in n boxes, some box holds at least two objects."
  theoremName := "pigeonhole"

/-- An issue about infinite sequences, with a proof by well-foundedness. -/
def descentIssue : Issue where
  number := 29
  title := "Bounded monotone sequences of natural numbers"
  text := "Prove that every non-increasing infinite sequence of natural numbers is " ++
    "eventually constant."
  theoremName := "eventually_constant"

/-- An example issue, with the truth of its claim. -/
structure Example where
  issue : Issue
  /-- Whether the claim of the issue is true. -/
  holds : Bool

/-- All example issues. -/
def all : List Example :=
  [⟨evenIssue, true⟩, ⟨successorIssue, false⟩, ⟨rationalIssue, true⟩, ⟨primesIssue, true⟩,
   ⟨polynomialIssue, false⟩, ⟨partyIssue, true⟩, ⟨factorizationIssue, true⟩, ⟨fermatIssue, true⟩,
   ⟨realIssue, true⟩, ⟨pigeonholeIssue, true⟩, ⟨descentIssue, true⟩]

end Adversarial.Examples
