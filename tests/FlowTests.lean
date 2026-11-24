import Adversarial
import Harness

/-! The tests of the generic flow of `Adversarial.Flow`. Scripted agents reply
with fixed texts, so the tests need no backend and no server. They cover flows
of one, two and three phases, the returns to earlier phases, the drops of
agents and the floor `minAgents`, the limits of rounds and visits, each
decision of a supervisor, the replies outside the protocol, the failure of the
check, the errors of agents, the names of speakers, rule supervisors, the
decision words of a phase, the return after a refused acceptance and the
entries of the thread. -/

open AIBackend
open Adversarial
open Adversarial.Flow

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
  let second := (o.entries.toList.filter (·.visit == 2)).filter (·.round == 2)
  check f "dropped" (second.length == 2 && second.all (·.active == ["critic"]))
    (toString (second.map (·.active)))
  check f "restored" (activeAt o "sr" == ["critic", "judge"]) (toString (activeAt o "sr"))

/-- Test 6. `BACK` with a line `PHASE name` returns to that phase. -/
def backNamed (f : Failures) : IO Unit := do
  let last : Phase := {
    name := "review", agents := [← scripted "critic" ["OBJECTION the definition is wrong"]]
    supervisor := ← scripted "sr" ["BACK the definition is wrong\nPHASE draft", "ACCEPT"] }
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
    supervisor := ← scripted "s" ["BACK\nPHASE review"] }
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

/-- Test 11. Drops that would leave fewer than `minAgents` agents drop no agent. -/
def dropFloor (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review", minAgents := 2
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["NO OBJECTION"],
               ← scripted "c" ["NO OBJECTION"]]
    supervisor := ← scripted "s" ["CONTINUE", "ACCEPT"] }] } start
  check f "active" (activeAt o "s" == ["a", "b", "c"]) (toString (activeAt o "s"))

/-- Test 12. Drops that leave exactly `minAgents` agents take effect. -/
def dropExact (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review", minAgents := 2
    agents := [← scripted "a" ["OBJECTION one"], ← scripted "b" ["OBJECTION two"],
               ← scripted "c" ["OBJECTION three"]]
    supervisor := ← scripted "s" ["CONTINUE\nDROP c", "ACCEPT"] }] } start
  check f "active" (activeAt o "s" == ["a", "b"]) (toString (activeAt o "s"))
  check f "below" (remaining ["a", "b", "c", "d"] ["a", "c", "d"] ["d", "c"] 2 == ["a", "b", "c", "d"])
  check f "exact" (remaining ["a", "b", "c", "d"] ["a", "c", "d"] ["d", "c"] 1 == ["a"])

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
  check f "flow-name" (← fails { name := "", phases := #[← quietPhase "pr"] })
  check f "shared-speaker" (← fails { phases := #[{ (← quietPhase "pr") with checker := "pr-agent" }] })
  check f "empty-thread" (← fails { phases := #[← quietPhase "pr"] } #[])

/-- Test 20. Each turn of the thread has an entry with its phase, visit,
round, kind and active agents. -/
def entries (f : Failures) : IO Unit := do
  let pr : Phase := {
    name := "pr", author := some (← scripted "prover" ["v1", "v2"])
    agents := [← scripted "challenger" ["OBJECTION x", "NO OBJECTION"]]
    supervisor := ← scripted "sp" ["CONTINUE", "ACCEPT"] }
  let o ← Flow.run { name := "formalize", phases := #[pr, ← quietPhase "review"] } start
  check f "speakers" (o.thread.speakers == "claim" :: speakersOf o) (toString (speakersOf o))
  check f "flow" (o.entries.toList.all (·.flow == "formalize"))
  check f "texts" (o.thread.toList.drop 1 == o.entries.toList.map fun e => ({ speaker := e.speaker, text := e.text } : Turn))
  check f "kinds" (o.entries.toList.map (·.kind) == [.work, .check, .objection, .decision,
    .work, .check, .noObjection, .decision, .noObjection, .decision])
  check f "phases" (o.entries.toList.map (·.phase) ==
    List.replicate 8 "pr" ++ List.replicate 2 "review")
  check f "visits" (o.entries.toList.map (·.visit) == List.replicate 8 1 ++ List.replicate 2 2)
  check f "rounds" (o.entries.toList.map (·.round) == [1, 1, 1, 1, 2, 2, 2, 2, 1, 1])
  check f "active" (o.entries.toList.all (·.active.length == 1))

/-- Test 21. Marks before `NO OBJECTION` do not make the reply an objection. -/
def noObjectionMarks (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "review"
    agents := [← scripted "a" ["**NO OBJECTION.** the statement matches"], ← scripted "b" ["OBJECTION x"]]
    supervisor := ← scripted "s" ["CONTINUE", "ACCEPT"] }] } start
  check f "kind" ((o.entries.toList.find? (·.speaker == "a")).any (·.kind == .noObjection))
  check f "active" (activeAt o "s" == ["b"]) (toString (activeAt o "s"))

/-- Test 22. A failed check allows `CONTINUE` without an objection, so the
author can repair the work. -/
def continueFailedCheck (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "pr", author := some (← scripted "prover" ["bad", "good"])
    check := fun work => pure (if work == "good" then none else some "the proof has a gap")
    agents := [← scripted "a" ["NO OBJECTION"]]
    supervisor := ← scripted "s" ["CONTINUE repair the proof", "ACCEPT"] }] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "work" (o.work == "good") o.work
  check f "active" (activeAt o "s" == ["a"]) (toString (activeAt o "s"))

/-- Test 23. A `PHASE` line with an unknown name, or with two names, is
outside the protocol. -/
def backUnknown (f : Failures) : IO Unit := do
  let flowWith (reply : String) : IO Flow := do
    return { phases := #[← quietPhase "draft", {
      name := "review", agents := [← scripted "a" ["OBJECTION x"]]
      supervisor := ← scripted "s" [reply] }] }
  let unknown ← errorOf ((← flowWith "BACK\nPHASE drfat").run start)
  check f "unknown" (unknown.any (has · "no phase has the name drfat")) (toString unknown)
  let two ← errorOf ((← flowWith "BACK\nPHASE draft, review").run start)
  check f "two" (two.any (has · "more than one phase")) (toString two)

/-- Test 24. Each speaker of a phase has a plain name, so a `DROP` line can
name every agent. -/
def speakerNames (f : Failures) : IO Unit := do
  let e ← errorOf (Flow.run { phases := #[{
    name := "review", agents := [← scripted "critic, senior" ["OBJECTION x"]]
    supervisor := ← scripted "s" ["ACCEPT"] }] } start)
  check f "comma" (e.any (has · "has no plain name")) (toString e)
  let checker ← errorOf (Flow.run { phases := #[{ (← quietPhase "pr") with checker := "lean 4" }] } start)
  check f "checker" (checker.any (has · "has no plain name")) (toString checker)

/-- Test 25. A rule supervisor decides from the round and adds no turn. -/
def ruleSupervisor (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "pr", author := some (← scripted "prover" ["v1", "v2"])
    agents := [← scripted "a" ["OBJECTION x"]]
    supervisor := .rule fun v => if v.round == 2 && v.passed then .accept else .continueDebate }] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "speakers" (o.thread.speakers == ["claim", "prover", "check", "a", "prover", "check", "a"])
    (toString o.thread.speakers)
  check f "no-decision" (o.entries.toList.all (·.kind != .decision))

/-- Test 26. A phase names its decisions by words of its own. -/
def phaseWords (f : Failures) : IO Unit := do
  let review (reply : String) (words : List (String × Word)) : IO Flow := do
    return { phases := #[{ name := "review", agents := [← scripted "a" ["NO OBJECTION"]]
                           supervisor := ← scripted "s" [reply], words }] }
  let custom := [("APPROVE", Word.accept), ("DENY", Word.reject)]
  let o ← (← review "APPROVE" custom).run start
  check f "approve" (o.status == .accepted) (repr o.status).pretty
  let e ← errorOf ((← review "ACCEPT" custom).run start)
  check f "default-word" (e.any (has · "not one of APPROVE, DENY")) (toString e)
  let bad ← errorOf ((← review "OK" [("OK2", Word.accept)]).run start)
  check f "letters" (bad.any (has · "decision words")) (toString bad)

/-- Test 27. A refused final acceptance returns to the latest phase with an
author. An earlier phase may accept work whose check failed. -/
def refusalReturns (f : Failures) : IO Unit := do
  let draft : Phase := {
    name := "draft", author := some (← scripted "prover" ["bad", expect "REFUSED" "good"])
    check := fun w => pure (if w == "good" then none else some "gap")
    report := fun r => if r.isNone then "PASS" else "FAIL"
    agents := [← scripted "a" ["NO OBJECTION"]], supervisor := ← scripted "sd" ["ACCEPT"] }
  let review : Phase := {
    name := "review", refusal := "REFUSED", agents := [← scripted "b" ["NO OBJECTION"]]
    supervisor := ← scripted "sr" ["ACCEPT"] }
  let o ← Flow.run { phases := #[draft, review] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "visits" (o.visits == 4) (toString o.visits)
  check f "reports" (o.thread.turnsOf "check" == ["FAIL", "REFUSED", "PASS"])
    (toString (o.thread.turnsOf "check"))

/-- Test 28. The failed check of a phase that is not binding reports the
failure and blocks no acceptance. -/
def evidenceOnly (f : Failures) : IO Unit := do
  let o ← Flow.run { phases := #[{
    name := "claim", binding := false, author := some (← scripted "proponent" ["garbled"])
    check := fun _ => pure (some "the statement does not occur in the source")
    agents := [← scripted "a" ["NO OBJECTION"]], supervisor := ← scripted "s" ["ACCEPT"] }] } start
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "report" (o.thread.turnsOf "check" == ["The check fails. the statement does not occur in the source"])
    (toString (o.thread.turnsOf "check"))

/-- Test 29. The flow calls `onDecision` after each decision, with the state so far. -/
def onDecision (f : Failures) : IO Unit := do
  let seen ← IO.mkRef (#[] : Array Snapshot)
  let pr : Phase := {
    name := "pr", author := some (← scripted "prover" ["v1", "v2"])
    agents := [← scripted "challenger" ["OBJECTION x", "NO OBJECTION"]]
    supervisor := .rule fun v => if v.objectors.isEmpty then .accept else .continueDebate }
  let o ← Flow.run { phases := #[pr, ← quietPhase "review"], onDecision := fun s => seen.modify (·.push s) } start
  let s ← seen.get
  check f "status" (o.status == .accepted) (repr o.status).pretty
  check f "decisions" ((s.toList.map fun x => (x.phase, x.round, x.decision)) ==
    [("pr", 1, .continueDebate), ("pr", 2, .accept), ("review", 1, .accept)])
  check f "reply" ((s.toList.map (·.reply)) == ["", "", "ACCEPT"])
  check f "work" ((s.toList.map (·.work)) == ["v1", "v2", "v2"])
  check f "thread" ((s.toList.getLast?.map (·.thread.size)) == some o.thread.size)

def tests : List (String × (Failures → IO Unit)) := [
  ("one-phase", onePhase), ("two-rounds", twoRounds), ("two-phases", twoPhases),
  ("three-phases", threePhases), ("back-previous", backPrevious), ("back-named", backNamed),
  ("back-first", backFirst), ("back-later", backLater), ("drop-quiet", dropQuiet),
  ("drop-named", dropNamed), ("drop-floor", dropFloor), ("drop-exact", dropExact),
  ("round-limit", roundLimit), ("visit-limit", visitLimit), ("reject", reject),
  ("continue-quiet", continueQuiet), ("protocol", protocol), ("check-failure", checkFailure),
  ("errors", errors), ("entries", entries), ("no-objection-marks", noObjectionMarks),
  ("continue-failed-check", continueFailedCheck), ("back-unknown", backUnknown),
  ("speaker-names", speakerNames), ("rule-supervisor", ruleSupervisor), ("phase-words", phaseWords),
  ("refusal-returns", refusalReturns), ("evidence-only", evidenceOnly), ("on-decision", onDecision)]

def main : IO Unit := runTests "flow" tests
