import Adversarial.Agent

/-! The generic flow.

A `Flow` is a sequence of phases. In each phase a supervisor manages a set of
agents over rounds. In a round the author of the phase, if the phase has one,
writes the work, and the check of the phase reports on it. Then each active
agent states an objection or none, and the supervisor decides. The decision
continues the debate, accepts the work of the phase, sends the flow back to an
earlier phase or rejects the work. A flow with one phase is the case `n = 1`
of the same code.

After a round that continues, the supervisor drops every agent without
objection and possibly more. When the drops would leave fewer agents than the
`minAgents` of the phase, no agent leaves. A return to a phase starts it again
with all its agents.

A supervisor is an agent, which replies on the thread, or a rule, which
decides from the round without a turn. Each phase has its own decision words,
such as `MERGE`, `REVISE` and `REJECT` for a review. -/

namespace Adversarial

open AIBackend

namespace Flow

/-- The text that opens the reply of an agent without objection. -/
def noObjectionMark : String := "NO OBJECTION"

/-- A decision word of a supervisor. The flow resolves the target of `back`. -/
inductive Word where
  | continueDebate
  | accept
  | back
  | reject
deriving BEq, Repr

/-- The decision words of a phase by default. -/
def defaultWords : List (String × Word) :=
  [("CONTINUE", .continueDebate), ("ACCEPT", .accept), ("BACK", .back), ("REJECT", .reject)]

/-- What a rule supervisor sees at the end of a round. -/
structure View where
  round : Nat
  maxRounds : Nat
  /-- Whether the last check of the flow passed. -/
  passed : Bool
  /-- The agents that objected in the round. -/
  objectors : List String

/-- The supervisor of a phase. An agent replies on the thread. A rule decides
from the round and adds no turn. -/
inductive Supervisor where
  | agent (a : Agent)
  | rule (decide : View → Word)

instance : Coe Agent Supervisor := ⟨.agent⟩

/-- The report of a check on the thread by default. -/
def defaultReport : Option String → String
  | none => "The check passes."
  | some reason => s!"The check fails. {reason}"

/-- One phase of a flow. -/
structure Phase where
  /-- The name of the phase. It consists of letters, digits, `_` and `-`,
  since a supervisor names it after `BACK`. -/
  name : String
  /-- The agent that writes the work in each round, if the phase has one. -/
  author : Option Agent := none
  /-- The check of the work. It returns the reason of a failure, or `none`
  when the work passes. -/
  check : String → IO (Option String) := fun _ => pure none
  /-- The speaker of the reports of the check. -/
  checker : String := "check"
  /-- Whether a failed check blocks the final acceptance. Without it, the
  report of the check is evidence for the agents only. -/
  binding : Bool := true
  /-- The agents that examine the work. -/
  agents : List Agent
  /-- The supervisor that decides at the end of each round. -/
  supervisor : Supervisor
  /-- The decision words of the supervisor and their meaning. -/
  words : List (String × Word) := defaultWords
  /-- The report of the check on the thread, from the reason of a failure. -/
  report : Option String → String := defaultReport
  /-- The notice of a refused acceptance. -/
  refusal : String := "The acceptance did not happen, since the check of the last work failed."
  /-- The largest number of rounds of one visit to the phase. -/
  maxRounds : Nat := 3
  /-- The least number of agents that the drops of a round may leave. -/
  minAgents : Nat := 1

/-- A decision of a supervisor. -/
inductive Decision where
  /-- Another round of the phase, word `CONTINUE`. -/
  | continueDebate
  /-- The work passes the phase, word `ACCEPT`. -/
  | accept
  /-- The flow returns to the earlier phase with this index, word `BACK`. -/
  | back (phase : Nat)
  /-- The flow ends without the work, word `REJECT`. -/
  | reject
deriving BEq, Repr

/-- The role of a turn in a flow. -/
inductive Kind where
  | work
  | check
  | objection
  | noObjection
  | decision
  /-- A report of the flow itself, such as a refused acceptance. -/
  | notice
deriving BEq, Repr

/-- One turn of a flow, with its position in the flow. -/
structure Entry where
  flow : String
  phase : String
  /-- The visit to a phase, counted from 1 over the whole flow. -/
  visit : Nat
  round : Nat
  speaker : String
  text : String
  kind : Kind
  /-- The agents active in the round. -/
  active : List String
  /-- The duration of the turn in milliseconds, for a reply or a check. -/
  ms : Nat
deriving BEq, Repr

inductive Status where
  | accepted
  | rejected
  /-- The flow reached a limit of rounds or of visits without a decision. -/
  | undecided
deriving BEq, Repr

/-- The end of a flow. -/
structure Outcome where
  status : Status
  /-- The last work of an author. -/
  work : String
  /-- The name of the last phase that ran. -/
  phase : String
  /-- The number of visits to phases. -/
  visits : Nat
  /-- The last reply of a supervisor. -/
  verdict : String
  thread : Thread
  entries : Array Entry

/-- Whether `s` is a nonempty word of letters, digits, `_` and `-`. -/
def plainName (s : String) : Bool :=
  !s.isEmpty && s.all fun c => c.isAlphanum || c == '_' || c == '-'

/-- The first word of a reply, after any leading marks such as `**`. -/
def firstWord (reply : String) : String :=
  String.ofList ((reply.toList.dropWhile (!·.isAlpha)).takeWhile Char.isAlpha)

/-- Whether a reply of an agent has no objection. The reply starts with
`NO OBJECTION`, after any leading marks such as `**`. -/
def isNoObjection (reply : String) : Bool :=
  (String.ofList (reply.toList.dropWhile (!·.isAlpha))).startsWith noObjectionMark

/-- The names that the lines of a reply with the keyword `key` hold, in order.
Such a line holds the keyword and names separated by commas, as in `DROP a, b`. -/
def lineNames (key reply : String) : List String :=
  (reply.splitOn "\n").flatMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith s!"{key} " then
      (((String.ofList (line.toList.drop (key.length + 1))).splitOn ",").map
        (·.trimAscii.toString)).filter (!·.isEmpty)
    else []

/-- The agents that the `DROP` lines of a reply name, in order. -/
def drops (reply : String) : List String := lineNames "DROP" reply

/-- The decision of a word in the phase with index `index`. For `back`, a
line `PHASE name` of the reply names an earlier phase. Without that line the
flow returns to the previous phase. -/
def resolve (phases : Array Phase) (index : Nat) (word : Word) (reply : String) :
    Except String Decision :=
  match word with
  | .continueDebate => .ok .continueDebate
  | .accept => .ok .accept
  | .reject => .ok .reject
  | .back =>
    match lineNames "PHASE" reply with
    | [] =>
      if index > 0 then .ok (.back (index - 1))
      else .error "the first phase has no earlier phase"
    | [target] =>
      match phases.findIdx? (·.name == target) with
      | some i =>
        if i < index then .ok (.back i)
        else .error s!"the phase {target} is not earlier than the current phase"
      | none => .error s!"no phase has the name {target}"
    | _ => .error "the reply names more than one phase"

/-- The decision of a reply of the supervisor of the phase with index
`index`. The first word of the reply is one of the words of the phase. -/
def parseDecision (phases : Array Phase) (index : Nat) (reply : String) : Except String Decision :=
  let words := (phases[index]?.map (·.words)).getD defaultWords
  match (words.find? (·.1 == firstWord reply)).map (·.2) with
  | some word => resolve phases index word reply
  | none => .error s!"the first word is not one of {", ".intercalate (words.map (·.1))}"

/-- The agents that stay active after a round that continues. The supervisor
drops every agent without objection and the agents that it names. When fewer
than `minAgents` agents would stay, no agent leaves. The result keeps the
order of `active`. -/
def remaining (active objectors named : List String) (minAgents : Nat) : List String :=
  let kept := active.filter fun a => objectors.contains a && !named.contains a
  if kept.length < minAgents then active else kept

end Flow

/-- The state of a flow after a decision of a supervisor. -/
structure Flow.Snapshot where
  phase : String
  visit : Nat
  round : Nat
  decision : Flow.Decision
  /-- The reply of an agent supervisor, or the empty string for a rule. -/
  reply : String
  /-- The last work of an author. -/
  work : String
  thread : Thread
  entries : Array Flow.Entry

/-- A flow, as a sequence of phases. -/
structure Flow where
  /-- The name of the flow, a plain word. Each entry carries it. -/
  name : String := "flow"
  phases : Array Flow.Phase
  /-- The largest number of visits to phases over the whole flow. It bounds
  the returns to earlier phases. -/
  maxVisits : Nat := 8
  /-- An action after each decision of a supervisor, before the flow applies
  it, such as a commit of the thread. -/
  onDecision : Flow.Snapshot → IO Unit := fun _ => pure ()

namespace Flow

/-- The preconditions of a flow. -/
def validate (flow : Flow) : IO Unit := do
  ensure (!flow.phases.isEmpty) "the flow has no phase"
  ensure (flow.maxVisits > 0) "the flow allows no visit"
  ensure (plainName flow.name) "the flow name is not a plain word"
  let names := flow.phases.toList.map (·.name)
  ensure (names.all plainName) "a phase name is not a plain word"
  ensure (names.eraseDups.length == names.length) "two phases share a name"
  for p in flow.phases do
    ensure (p.maxRounds > 0) s!"the phase {p.name} has no round"
    ensure (!p.agents.isEmpty) s!"the phase {p.name} has no agent"
    ensure (p.minAgents ≤ p.agents.length) s!"the phase {p.name} has fewer agents than minAgents"
    let supervisor := match p.supervisor with
      | .agent a => [a.name]
      | .rule _ => []
    let speakers := p.checker :: supervisor ++
      ((p.author.map (·.name)).toList ++ p.agents.map (·.name))
    let words := p.words.map (·.1)
    ensure (!words.isEmpty && words.all (fun w => !w.isEmpty && w.all Char.isAlpha) &&
      words.eraseDups.length == words.length) s!"the decision words of the phase {p.name} are not distinct words of letters"
    -- A `DROP` line names agents, so a name holds no comma and no space.
    ensure (speakers.all plainName) s!"a speaker of the phase {p.name} has no plain name"
    ensure (speakers.eraseDups.length == speakers.length)
      s!"two speakers of the phase {p.name} share a name"

/-- An `IO` error for a reply of a supervisor outside the protocol. -/
def protocolError (reason reply : String) : IO.Error :=
  IO.userError s!"the reply of the supervisor is outside the protocol, since {reason}: {reply}"

/-- Runs the flow on the thread `start`, from the first phase.

In each round of a phase the author writes the work, and the check reports on
it under the name of the checker. Each active agent replies. A reply that
starts with `NO OBJECTION`, after any marks such as `**`, has no objection,
and any other reply is an objection. The supervisor replies last. The first
word of its reply is the decision, after any marks. The words below are the default ones, and a phase
may name each meaning by other words. A rule supervisor decides by a function
of the round and adds no turn.

* `CONTINUE` starts another round. It requires an agent with an objection or
  a failed last check. The lines `DROP a, b` of the reply name further agents
  to drop.
* `ACCEPT` moves the flow to the next phase, or ends it with the status
  `accepted` after the last phase. When the last check of the flow failed, the
  flow refuses the final acceptance on the thread. The latest phase with an
  author then writes the work again, in another round of the current phase or
  after a return to an earlier phase.
* `BACK` returns to an earlier phase, the one that a line `PHASE name` names
  or else the previous one.
* `REJECT` ends the flow with the status `rejected`.

A phase whose check is not `binding` reports a failed check, and the failure
blocks no acceptance. After each decision the flow calls `onDecision` with the
state so far.

The flow raises an `IO` error on any other reply, and when an agent raises
one. It ends with the status `undecided` after `maxRounds` rounds of a phase
or `maxVisits` visits. -/
def run (flow : Flow) (start : Thread) : IO Outcome := do
  validate flow
  ensure (!start.isEmpty) "the thread is empty"
  let mut thread := start
  let mut entries : Array Entry := #[]
  let mut work := ""
  let mut passed := true
  let mut verdict := ""
  let mut index := 0
  let mut last := ""
  for visit in [1:flow.maxVisits + 1] do
    let some phase := flow.phases[index]? | throw (IO.userError "the flow lost its phase")
    last := phase.name
    let mut active := phase.agents.map (·.name)
    let mut next : Option Nat := none
    let mut final : Option Status := none
    for round in [1:phase.maxRounds + 1] do
      let entry (speaker text : String) (kind : Kind) (ms : Nat := 0) : Entry :=
        { flow := flow.name, phase := phase.name, visit, round, speaker, text, kind, active, ms }
      if let some author := phase.author then
        let t0 ← IO.monoMsNow
        let (text, t) ← author.reply thread
        let t1 ← IO.monoMsNow
        work := text
        let failure ← phase.check text
        let t2 ← IO.monoMsNow
        passed := failure.isNone || !phase.binding
        let report := phase.report failure
        thread := t.push { speaker := phase.checker, text := report }
        entries := (entries.push (entry author.name text .work (t1 - t0))).push
          (entry phase.checker report .check (t2 - t1))
      let mut objectors : List String := []
      for agent in phase.agents do
        if active.contains agent.name then
          let t0 ← IO.monoMsNow
          let (text, t) ← agent.reply thread
          let t1 ← IO.monoMsNow
          thread := t
          let objects := !isNoObjection text
          if objects then objectors := objectors ++ [agent.name]
          entries := entries.push
            (entry agent.name text (if objects then .objection else .noObjection) (t1 - t0))
      let mut reply := "(the rule of the phase)"
      let mut named : List String := []
      let mut decision : Decision := .continueDebate
      match phase.supervisor with
      | .agent s =>
        let t0 ← IO.monoMsNow
        let (text, t) ← s.reply thread
        let t1 ← IO.monoMsNow
        thread := t
        verdict := text
        reply := text
        entries := entries.push (entry s.name text .decision (t1 - t0))
        decision ← match parseDecision flow.phases index text with
          | .ok d => pure d
          | .error reason => throw (protocolError reason text)
        named := (drops text).eraseDups
        if let some name := named.find? (!active.contains ·) then
          throw (protocolError s!"the agent {name} is not active" text)
      | .rule decide =>
        let word := decide { round, maxRounds := phase.maxRounds, passed, objectors }
        decision ← match resolve flow.phases index word "" with
          | .ok d => pure d
          | .error reason => throw (protocolError reason reply)
      flow.onDecision { phase := phase.name, visit, round, decision, work, thread, entries
                        reply := if let .agent _ := phase.supervisor then reply else "" }
      match decision with
      | .continueDebate =>
        if objectors.isEmpty && passed then
          throw (protocolError "no agent objects and the last check passed" reply)
        active := remaining active objectors named phase.minAgents
      | .accept =>
        if passed || index + 1 < flow.phases.size then
          next := some (index + 1)
          break
        thread := thread.push { speaker := phase.checker, text := phase.refusal }
        entries := entries.push (entry phase.checker phase.refusal .notice)
        -- The latest phase with an author writes the work again.
        if phase.author.isNone then
          let authored := (List.range index).reverse.find? fun i =>
            (flow.phases[i]?.bind (·.author)).isSome
          if let some i := authored then
            next := some i
            break
      | .back i =>
        next := some i
        break
      | .reject =>
        final := some .rejected
        break
    if let some status := final then
      return { status, work, phase := last, visits := visit, verdict, thread, entries }
    match next with
    | none => return { status := .undecided, work, phase := last, visits := visit, verdict, thread, entries }
    | some i =>
      if i == flow.phases.size then
        return { status := .accepted, work, phase := last, visits := visit, verdict, thread, entries }
      index := i
  return { status := .undecided, work, phase := last, visits := flow.maxVisits, verdict, thread, entries }

end Flow

end Adversarial
