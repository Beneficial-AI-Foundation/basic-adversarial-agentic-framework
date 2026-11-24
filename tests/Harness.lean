import Adversarial

/-! The test harness of the executables `flowtests` and `prtests`. Scripted
agents reply with fixed texts, so the tests need no backend and no server. -/

open Adversarial

/-- A mutable count of failures, reported at the end. -/
abbrev Failures := IO.Ref Nat

def check (f : Failures) (name : String) (cond : Bool) (detail : String := "") : IO Unit := do
  unless cond do
    f.modify (· + 1)
    IO.eprintln s!"FAIL {name} {detail}"

/-- The text of the `IO` error that an action raises, if it raises one. -/
def errorOf {α : Type} (act : IO α) : IO (Option String) := do
  try
    let _ ← act
    return none
  catch e => return some (toString e)

/-- Whether `pattern` occurs in `s`. -/
def has (s pattern : String) : Bool := (s.splitOn pattern).length > 1

/-- A script part that fails unless the thread contains `want`. -/
def expect (want reply : String) : String := s!"EXPECT {want}\n{reply}"

/-- A scripted agent. It replies with the parts of `script` in order, one per
turn, and repeats the last one. A part made by `expect` raises an `IO` error
when the prompt lacks the expected text. -/
def scripted (name : String) (script : List String) : IO Agent := do
  let step ← IO.mkRef 0
  let ask (prompt : String) : IO String := do
    let i ← step.modifyGet fun i => (i, i + 1)
    let part := script.getD i (script.getLastD "")
    match part.splitOn "\n" with
    | first :: rest =>
      if first.startsWith "EXPECT " then
        let want := String.ofList (first.toList.drop 7)
        unless has prompt want do
          throw (IO.userError s!"the agent {name} expected the text {want} in the thread")
        return "\n".intercalate rest
      return part
    | [] => return part
  return { name, backend := { name := "scripted", ask }, instructions := s!"You are {name}." }

/-- An agent whose backend always raises an `IO` error. -/
def failing (name : String) : Agent :=
  { name, instructions := s!"You are {name}."
    backend := { name := "failing", ask := fun _ => throw (IO.userError s!"{name} lost its connection") } }

/-- Runs named tests, each with a count of its own failures. An error that
escapes a test counts as one failure. Raises an `IO` error after any failure. -/
def runTests (label : String) (tests : List (String × (Failures → IO Unit))) : IO Unit := do
  let mut failures := 0
  for (name, test) in tests do
    let count : Failures ← IO.mkRef 0
    match ← (test count).toBaseIO with
    | .ok () => pure ()
    | .error e => check count "uncaught" false (toString e)
    let n ← count.get
    failures := failures + n
    IO.println s!"test {name}: {if n == 0 then "ok" else s!"FAILED ({n})"}"
  if failures != 0 then throw (IO.userError s!"{failures} failures")
  IO.println s!"all {tests.length} {label} tests passed"
