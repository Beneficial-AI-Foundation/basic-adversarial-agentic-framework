import Adversarial

/-! The tests of the generic flow of `Adversarial.Flow`. Scripted agents reply
with fixed texts, so the tests need no backend and no server. The twenty
tests cover flows of one, two and three phases, the returns to earlier phases,
the drops of agents and the floor `minAgents`, the limits of rounds and
visits, each decision of a supervisor, the replies outside the protocol, the
failure of the check, the errors of agents and the contents of the thread. -/

open AIBackend
open Adversarial
open Adversarial.Flow

/-! ## The test harness -/

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

def start : Thread := #[{ speaker := "claim", text := "The sum of two even numbers is even." }]

/-- A phase with one agent without objection and a supervisor that accepts. -/
def quietPhase (name : String) : IO Phase := do
  return { name, agents := [← scripted s!"{name}-agent" ["NO OBJECTION"]],
           supervisor := ← scripted s!"{name}-supervisor" ["ACCEPT"] }

/-- The speakers of the turns of the entries. -/
def speakersOf (o : Flow.Outcome) : List String := o.entries.toList.map (·.speaker)

/-- The active agents of the last turn of `speaker`. -/
def activeAt (o : Flow.Outcome) (speaker : String) : List String :=
  ((o.entries.toList.filter (·.speaker == speaker)).getLast?.map (·.active)).getD []

/-! ## The tests -/

/-- Test 1. One phase whose only round ends in an acceptance. -/
def onePhase (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[← quietPhase "review"] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "visits" (o.visits == 1) (toString o.visits)
  check f "phase" (o.phase == "review") o.phase
  check f "speakers" (o.thread.speakers == ["claim", "review-agent", "review-supervisor"])
    (toString o.thread.speakers)

/-- Test 2. One phase with two rounds. The objection of the first round leads
to `CONTINUE`, and the second round accepts. -/
def twoRounds (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review"
    agents := [← scripted "a" ["OBJECTION the case n = 0 is missing", expect "CONTINUE" "NO OBJECTION"]]
    supervisor := ← scripted "s" [expect "the case n = 0" "CONTINUE treat n = 0", "ACCEPT"] }] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "speakers" (o.thread.speakers == ["claim", "a", "s", "a", "s"]) (toString o.thread.speakers)
  check f "rounds" (o.entries.toList.map (·.round) == [1, 1, 2, 2])

/-- Test 3. Two phases with an author in the first. The second phase reads the
work of the first. -/
def twoPhases (f : Failures) : IO Unit := do
  let pr : Phase := {
    name := "pr", author := some (← scripted "prover" ["theorem even_add"])
    agents := [← scripted "challenger" ["NO OBJECTION"]], supervisor := ← scripted "sp" ["ACCEPT"] }
  let review : Phase := {
    name := "review", agents := [← scripted "critic" ["NO OBJECTION"]]
    supervisor := ← scripted "sr" [expect "theorem even_add" "ACCEPT"] }
  let o ← Flow.run { phases := #[pr, review] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "work" (o.work == "theorem even_add") o.work
  check f "visits" (o.visits == 2) (toString o.visits)
  check f "speakers" (o.thread.speakers ==
    ["claim", "prover", "check", "challenger", "sp", "critic", "sr"]) (toString o.thread.speakers)

/-- Test 4. Three phases run by the same code in order. -/
def threePhases (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[← quietPhase "one", ← quietPhase "two", ← quietPhase "three"] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "visits" (o.visits == 3) (toString o.visits)
  check f "phases" ((o.entries.toList.map (·.phase)).eraseDups == ["one", "two", "three"])
  check f "turns" (o.thread.size == 7) (toString o.thread.size)

/-- Test 5. `BACK` without a phase name returns to the previous phase. The
return starts the phase again with all its agents. -/
def backPrevious (f : Failures) : IO Unit := do
  let pr : Phase := {
    name := "pr", author := some (← scripted "prover" ["v1", expect "BACK" "v2"])
    agents := [← scripted "challenger" ["NO OBJECTION"]], supervisor := ← scripted "sp" ["ACCEPT"] }
  let review : Phase := {
    name := "review"
    agents := [← scripted "critic" ["OBJECTION v1 is weaker than the claim", "NO OBJECTION"],
               ← scripted "judge" ["NO OBJECTION"]]
    supervisor := ← scripted "sr" ["CONTINUE", "BACK strengthen the statement", expect "v2" "ACCEPT"] }
  let o ← Flow.run { phases := #[pr, review] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "visits" (o.visits == 4) (toString o.visits)
  check f "work" (o.work == "v2") o.work
  check f "dropped" (((o.entries.toList.filter (·.visit == 2)).filter (·.round == 2)).all
    (·.active == ["critic"]))
  check f "restored" (activeAt o "sr" == ["critic", "judge"]) (toString (activeAt o "sr"))

/-- Test 6. `BACK` with the name of a phase returns to that phase. -/
def backNamed (f : Failures) : IO Unit := do
  let last : Phase := {
    name := "review", agents := [← scripted "critic" ["OBJECTION the definition is wrong"]]
    supervisor := ← scripted "sr" ["BACK draft the definition is wrong", "ACCEPT"] }
  let o ← Flow.run { phases := #[← quietPhase "draft", ← quietPhase "pr", last] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  let visits := (o.entries.toList.map fun e => (e.visit, e.phase)).eraseDups.map (·.2)
  check f "visits" (visits == ["draft", "pr", "review", "draft", "pr", "review"]) (toString visits)

/-- Test 7. `BACK` in the first phase is outside the protocol. -/
def backFirst (f : Failures) : IO Unit := do
  let e ← errorOf (Flow.run { phases := #[{
    name := "pr", agents := [← scripted "a" ["OBJECTION x"]]
    supervisor := ← scripted "s" ["BACK"] }] } start)
  check f "error" (e.any (has · "no earlier phase")) (toString e)

/-- Test 8. `BACK` that names the current phase is outside the protocol. -/
def backLater (f : Failures) : IO Unit := do
  let review : Phase := {
    name := "review", agents := [← scripted "a" ["OBJECTION x"]]
    supervisor := ← scripted "s" ["BACK review"] }
  let e ← errorOf (Flow.run { phases := #[← quietPhase "pr", review] } start)
  check f "error" (e.any (has · "not earlier than the current phase")) (toString e)

/-- Test 9. After `CONTINUE` the agents without objection leave. -/
def dropQuiet (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review"
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["NO OBJECTION"],
               ← scripted "c" ["OBJECTION two"]]
    supervisor := ← scripted "s" ["CONTINUE", "ACCEPT"] }] } start
  check f "speakers" (o.thread.speakers == ["claim", "a", "b", "c", "s", "a", "c", "s"])
    (toString o.thread.speakers)
  check f "active" (activeAt o "s" == ["a", "c"]) (toString (activeAt o "s"))

/-- Test 10. A `DROP` line removes an agent with an objection. -/
def dropNamed (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review"
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["OBJECTION two"],
               ← scripted "c" ["OBJECTION three"]]
    supervisor := ← scripted "s" ["CONTINUE the objection of b repeats a\nDROP b", "ACCEPT"] }] } start
  check f "active" (activeAt o "s" == ["a", "c"]) (toString (activeAt o "s"))

/-- Test 11. No drop goes below `minAgents`. An agent without objection returns. -/
def dropFloor (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review", minAgents := 2
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["NO OBJECTION"],
               ← scripted "c" ["NO OBJECTION"]]
    supervisor := ← scripted "s" ["CONTINUE", "ACCEPT"] }] } start
  check f "active" (activeAt o "s" == ["a", "b"]) (toString (activeAt o "s"))

/-- Test 12. At the floor, the last named agent with an objection returns first. -/
def dropPriority (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review", minAgents := 2
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["OBJECTION two"],
               ← scripted "c" ["OBJECTION three"]]
    supervisor := ← scripted "s" ["CONTINUE\nDROP b, c", "ACCEPT"] }] } start
  check f "active" (activeAt o "s" == ["a", "c"]) (toString (activeAt o "s"))
  check f "remaining" (remaining ["a", "b", "c", "d"] ["a", "c", "d"] ["d", "c"] 2 == ["a", "c"])

/-- Test 13. A phase that reaches `maxRounds` ends the flow as undecided. -/
def roundLimit (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review", maxRounds := 2
    agents := [← scripted "a" ["OBJECTION x"]], supervisor := ← scripted "s" ["CONTINUE"] }] } start
  check f "status" (o.status == .undecided) (repr o.status).pretty
  check f "decisions" ((o.thread.turnsOf "s").length == 2)

/-- Test 14. A flow that reaches `maxVisits` ends as undecided. -/
def visitLimit (f : Failures) : IO Unit := do
  let review : Phase := {
    name := "review", agents := [← scripted "critic" ["OBJECTION x"]]
    supervisor := ← scripted "sr" ["BACK"] }
  let o ← Flow.run { phases := #[← quietPhase "pr", review], maxVisits := 5 } start
  check f "status" (o.status == .undecided) (repr o.status).pretty
  check f "visits" (o.visits == 5) (toString o.visits)
  check f "phase" (o.phase == "pr") o.phase

/-- Test 15. `REJECT` ends the flow. -/
def reject (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[← quietPhase "pr", {
    name := "review", agents := [← scripted "critic" ["OBJECTION 0 + 1 ≠ 0"]]
    supervisor := ← scripted "sr" ["REJECT the claim is false at n = 0"] }] } start
  check f "status" (o.status == .rejected) (repr o.status).pretty
  check f "phase" (o.phase == "review") o.phase
  check f "verdict" (has o.verdict "false at n = 0") o.verdict

/-- Test 16. `CONTINUE` without an objection is outside the protocol. -/
def continueQuiet (f : Failures) : IO Unit := do
  let e ← errorOf (Flow.run { phases := #[{
    name := "review", agents := [← scripted "a" ["NO OBJECTION"]]
    supervisor := ← scripted "s" ["CONTINUE"] }] } start)
  check f "error" (e.any (has · "no agent objects")) (toString e)

/-- Test 17. A reply with an unknown word or a `DROP` of an inactive agent is
outside the protocol. Marks before the word are not. -/
def protocol (f : Failures) : IO Unit := do
  let reviewWith (reply : String) : IO Flow := do
    return { phases := #[{ name := "review", agents := [← scripted "a" ["OBJECTION x"]]
                           supervisor := ← scripted "s" [reply] }] }
  let unknown ← errorOf ((← reviewWith "PERHAPS later").run start)
  check f "unknown-word" (unknown.any (has · "outside the protocol")) (toString unknown)
  let dropped ← errorOf ((← reviewWith "CONTINUE\nDROP z").run start)
  check f "drop-inactive" (dropped.any (has · "the agent z is not active")) (toString dropped)
  let marked ← (← reviewWith "**ACCEPT.** the claim holds").run start
  check f "marks" (marked.status == .accepted) (repr marked.status).pretty

/-- Test 18. The flow refuses an acceptance while the last check failed. -/
def checkFailure (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "pr", checker := "lean", author := some (← scripted "prover" ["bad", "good"])
    check := fun work => pure (if work == "good" then none else some "the proof has a gap")
    agents := [← scripted "a" ["NO OBJECTION"]]
    supervisor := ← scripted "s" ["ACCEPT", expect "The acceptance did not happen" "ACCEPT"] }] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "work" (o.work == "good") o.work
  check f "reports" (o.thread.turnsOf "lean" == ["The check fails. the proof has a gap",
    "The acceptance did not happen, since the check of the last work failed.", "The check passes."])
    (toString (o.thread.turnsOf "lean"))

/-- Test 19. The error of an agent stops the flow, and so does a violated
precondition. -/
def errors (f : Failures) : IO Unit := do
  let broken ← errorOf (Flow.run { phases := #[{
    name := "review", agents := [failing "a"], supervisor := ← scripted "s" ["ACCEPT"] }] } start)
  check f "agent" (broken.any (has · "a lost its connection")) (toString broken)
  let fails (flow : Flow) (t : Thread := start) : IO Bool := return (← errorOf (flow.run t)).isSome
  check f "no-phase" (← fails { phases := #[] })
  check f "shared-phase-name" (← fails { phases := #[← quietPhase "pr", ← quietPhase "pr"] })
  check f "phase-name" (← fails { phases := #[← quietPhase "two words"] })
  check f "min-agents" (← fails { phases := #[{ (← quietPhase "pr") with minAgents := 2 }] })
  check f "no-round" (← fails { phases := #[{ (← quietPhase "pr") with maxRounds := 0 }] })
  check f "shared-speaker" (← fails { phases := #[{ (← quietPhase "pr") with checker := "pr-agent" }] })
  check f "empty-thread" (← fails { phases := #[← quietPhase "pr"] } #[])

/-- Test 20. Each turn of the thread has an entry with its phase, visit,
round, kind and active agents. -/
def entries (f : Failures) : IO Unit := do
  let pr : Phase := {
    name := "pr", author := some (← scripted "prover" ["v1", "v2"])
    agents := [← scripted "challenger" ["OBJECTION x", "NO OBJECTION"]]
    supervisor := ← scripted "sp" ["CONTINUE", "ACCEPT"] }
  let o ← Flow.run { phases := #[pr, ← quietPhase "review"] } start
  check f "speakers" (o.thread.speakers == "claim" :: speakersOf o) (toString (speakersOf o))
  check f "texts" (o.thread.toList.drop 1 == o.entries.toList.map fun e => ({ speaker := e.speaker, text := e.text } : Turn))
  check f "kinds" (o.entries.toList.map (·.kind) == [.work, .check, .objection, .decision,
    .work, .check, .noObjection, .decision, .noObjection, .decision])
  check f "phases" (o.entries.toList.map (·.phase) ==
    List.replicate 8 "pr" ++ List.replicate 2 "review")
  check f "visits" (o.entries.toList.map (·.visit) == List.replicate 8 1 ++ List.replicate 2 2)
  check f "rounds" (o.entries.toList.map (·.round) == [1, 1, 1, 1, 2, 2, 2, 2, 1, 1])
  check f "active" (o.entries.toList.all (·.active.length == 1))

def tests : List (String × (Failures → IO Unit)) := [
  ("one-phase", onePhase), ("two-rounds", twoRounds), ("two-phases", twoPhases),
  ("three-phases", threePhases), ("back-previous", backPrevious), ("back-named", backNamed),
  ("back-first", backFirst), ("back-later", backLater), ("drop-quiet", dropQuiet),
  ("drop-named", dropNamed), ("drop-floor", dropFloor), ("drop-priority", dropPriority),
  ("round-limit", roundLimit), ("visit-limit", visitLimit), ("reject", reject),
  ("continue-quiet", continueQuiet), ("protocol", protocol), ("check-failure", checkFailure),
  ("errors", errors), ("entries", entries)]

def main : IO Unit := do
  let failures ← IO.mkRef 0
  for (name, test) in tests do
    let before ← failures.get
    let count : Failures ← IO.mkRef 0
    match ← (test count).toBaseIO with
    | .ok () => pure ()
    | .error e => check count "uncaught" false (toString e)
    let n ← count.get
    failures.set (before + n)
    IO.println s!"test {name}: {if n == 0 then "ok" else s!"FAILED ({n})"}"
  let fails ← failures.get
  if fails != 0 then throw (IO.userError s!"{fails} failures")
  IO.println s!"all {tests.length} flow tests passed"
