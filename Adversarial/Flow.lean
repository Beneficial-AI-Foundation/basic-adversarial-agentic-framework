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
objection and possibly more, never below the `minAgents` of the phase. A
return to a phase starts it again with all its agents. -/

namespace Adversarial

open AIBackend

namespace Flow

/-- The text that opens the reply of an agent without objection. -/
def noObjectionMark : String := "NO OBJECTION"

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
  /-- The agents that examine the work. -/
  agents : List Agent
  /-- The agent that decides at the end of each round. -/
  supervisor : Agent
  /-- The largest number of rounds of one visit to the phase. -/
  maxRounds : Nat := 3
  /-- The number of agents below which no drop goes. -/
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
  phase : String
  /-- The visit to a phase, counted from 1 over the whole flow. -/
  visit : Nat
  round : Nat
  speaker : String
  text : String
  kind : Kind
  /-- The agents active in the round. -/
  active : List String
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

/-- The word after the first word of a reply, or the empty string. -/
def secondWord (reply : String) : String :=
  let rest := ((reply.toList.dropWhile (!·.isAlpha)).dropWhile Char.isAlpha).dropWhile (· == ' ')
  String.ofList (rest.takeWhile fun c => c.isAlphanum || c == '_' || c == '-')

/-- The agents that the `DROP` lines of a reply name, in order. A `DROP` line
holds the word `DROP` and names separated by commas. -/
def drops (reply : String) : List String :=
  (reply.splitOn "\n").flatMap fun line =>
    let line := line.trimAscii.toString
    if line.startsWith "DROP " then
      (((String.ofList (line.toList.drop 5)).splitOn ",").map (·.trimAscii.toString)).filter
        (!·.isEmpty)
    else []

/-- The decision of the supervisor of the phase with index `index`. The word
`BACK` may name an earlier phase. Without the name of a phase it returns to the
previous phase. -/
def parseDecision (phases : Array Phase) (index : Nat) (reply : String) : Except String Decision :=
  match firstWord reply with
  | "CONTINUE" => .ok .continueDebate
  | "ACCEPT" => .ok .accept
  | "REJECT" => .ok .reject
  | "BACK" =>
    let target := secondWord reply
    match phases.findIdx? (·.name == target) with
    | some i =>
      if i < index then .ok (.back i)
      else .error s!"the phase {target} is not earlier than the current phase"
    | none =>
      if index > 0 then .ok (.back (index - 1))
      else .error "the first phase has no earlier phase"
  | _ => .error "the first word is not CONTINUE, ACCEPT, BACK or REJECT"

/-- The agents that stay active after a round that continues. The supervisor
drops every agent without objection and the agents that it names. When fewer
than `minAgents` agents stay, dropped agents return. The named agents with an
objection return first, the last named first, so a supervisor names them from
the weakest objection to the strongest. The agents without objection return
last. The result keeps the order of `active`. -/
def remaining (active objectors named : List String) (minAgents : Nat) : List String :=
  let kept := active.filter fun a => objectors.contains a && !named.contains a
  let restore := (named.filter objectors.contains).reverse ++ active.filter (!objectors.contains ·)
  let back := restore.take (minAgents - kept.length)
  active.filter fun a => kept.contains a || back.contains a

end Flow

/-- A flow, as a sequence of phases. -/
structure Flow where
  phases : Array Flow.Phase
  /-- The largest number of visits to phases over the whole flow. It bounds
  the returns to earlier phases. -/
  maxVisits : Nat := 8

namespace Flow

/-- The preconditions of a flow. -/
def validate (flow : Flow) : IO Unit := do
  ensure (!flow.phases.isEmpty) "the flow has no phase"
  ensure (flow.maxVisits > 0) "the flow allows no visit"
  let names := flow.phases.toList.map (·.name)
  ensure (names.all plainName) "a phase name is not a plain word"
  ensure (names.eraseDups.length == names.length) "two phases share a name"
  for p in flow.phases do
    ensure (p.maxRounds > 0) s!"the phase {p.name} has no round"
    ensure (!p.agents.isEmpty) s!"the phase {p.name} has no agent"
    ensure (p.minAgents ≤ p.agents.length) s!"the phase {p.name} has fewer agents than minAgents"
    ensure (plainName p.checker) s!"the checker of the phase {p.name} is not a plain word"
    let speakers := p.checker :: p.supervisor.name ::
      ((p.author.map (·.name)).toList ++ p.agents.map (·.name))
    ensure (speakers.eraseDups.length == speakers.length)
      s!"two speakers of the phase {p.name} share a name"

/-- An `IO` error for a reply of a supervisor outside the protocol. -/
def protocolError (reason reply : String) : IO.Error :=
  IO.userError s!"the reply of the supervisor is outside the protocol, since {reason}: {reply}"

/-- Runs the flow on the thread `start`, from the first phase.

In each round of a phase the author writes the work, and the check reports on
it under the name of the checker. Each active agent replies. A reply that
starts with `NO OBJECTION` has no objection, and any other reply is an
objection. The supervisor replies last. The first word of its reply is the
decision, after any marks such as `**`.

* `CONTINUE` starts another round. It requires an agent with an objection.
  The lines `DROP a, b` of the reply name further agents to drop.
* `ACCEPT` moves the flow to the next phase, or ends it with the status
  `accepted` after the last phase. When the last check of the flow failed, the
  flow refuses the acceptance on the thread and starts another round.
* `BACK` returns to an earlier phase, the one that the next word names or
  else the previous one.
* `REJECT` ends the flow with the status `rejected`.

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
      let entry (speaker text : String) (kind : Kind) : Entry :=
        { phase := phase.name, visit, round, speaker, text, kind, active }
      if let some author := phase.author then
        let (text, t) ← author.reply thread
        work := text
        let failure ← phase.check text
        passed := failure.isNone
        let report := match failure with
          | none => "The check passes."
          | some reason => s!"The check fails. {reason}"
        thread := t.push { speaker := phase.checker, text := report }
        entries := (entries.push (entry author.name text .work)).push
          (entry phase.checker report .check)
      let mut objectors : List String := []
      for agent in phase.agents do
        if active.contains agent.name then
          let (text, t) ← agent.reply thread
          thread := t
          let objects := !text.startsWith noObjectionMark
          if objects then objectors := objectors ++ [agent.name]
          entries := entries.push (entry agent.name text (if objects then .objection else .noObjection))
      let (reply, t) ← phase.supervisor.reply thread
      thread := t
      verdict := reply
      entries := entries.push (entry phase.supervisor.name reply .decision)
      let decision ← match parseDecision flow.phases index reply with
        | .ok d => pure d
        | .error reason => throw (protocolError reason reply)
      let named := (drops reply).eraseDups
      if let some name := named.find? (!active.contains ·) then
        throw (protocolError s!"the agent {name} is not active" reply)
      match decision with
      | .continueDebate =>
        if objectors.isEmpty then throw (protocolError "no agent objects" reply)
        active := remaining active objectors named phase.minAgents
      | .accept =>
        if passed then
          next := some (index + 1)
          break
        let notice := "The acceptance did not happen, since the check of the last work failed."
        thread := thread.push { speaker := phase.checker, text := notice }
        entries := entries.push (entry phase.checker notice .notice)
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
