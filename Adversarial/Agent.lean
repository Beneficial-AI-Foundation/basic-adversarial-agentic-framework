import AIBackend.Claude.Api
import AIBackend.Claude.Cli

/-! Claude agents over the Claude backends of the package `aibackend`.

An `Agent` is a Claude backend with a name and standing instructions. A
`Thread` is a conversation among several agents, such as the discussion of a
pull request. An agent reads the whole thread and adds one turn, so the thread
is the only state that the agents share. A `Pair` holds two adversarial agents
that debate on a thread.

Agents share no connection. `Agent.apiOwn` gives each agent a client of its
own, and each call of an `Agent.cli` agent is one isolated process. -/

namespace Adversarial

open AIBackend
open AIBackend.Claude

/-- A Claude agent. The constructors `Agent.api` and `Agent.cli` build one
over each Claude backend. -/
structure Agent where
  name : String := "agent"
  backend : Backend
  instructions : String

/-- One contribution to a thread. -/
structure Turn where
  speaker : String
  text : String
deriving Repr, BEq

/-- A conversation among several agents, in order. -/
abbrev Thread := Array Turn

namespace Thread

/-- The header line of the turns of `speaker` in a rendered thread. -/
def header (speaker : String) : String := s!"## {speaker}"

/-- The thread as text. A header line precedes each turn. A line of a turn
that starts like a header gains a leading space, so no turn can forge the
header of another speaker. -/
def render (t : Thread) : String :=
  "\n".intercalate (t.toList.map fun turn =>
    let body := (turn.text.splitOn "\n").map fun line =>
      if line.startsWith "## " then " " ++ line else line
    s!"{header turn.speaker}\n{"\n".intercalate body}\n")

/-- The speakers of the thread, in order. -/
def speakers (t : Thread) : List String := t.toList.map (·.speaker)

/-- The texts of the turns of `speaker`, in order. -/
def turnsOf (t : Thread) (speaker : String) : List String :=
  (t.toList.filter (·.speaker == speaker)).map (·.text)

end Thread

namespace Agent

/-- An agent over the Claude API backend of the client `c`. The agent uses
the connection of `c`. Agents that must share nothing need one client each,
which `apiOwn` provides. -/
def api (c : Api.Client) (name instructions : String) (model : String := Api.defaultModel)
    (maxTokens : Nat := Api.defaultMaxTokens) : Agent :=
  { name, backend := c.backend model maxTokens, instructions }

/-- An agent over the Claude API backend with a client of its own, hence with
a connection of its own. The key comes from `Api.Client.fromDefault`. -/
def apiOwn (name instructions : String) (model : String := Api.defaultModel)
    (maxTokens : Nat := Api.defaultMaxTokens) : IO Agent :=
  return api (← Api.Client.fromDefault) name instructions model maxTokens

/-- An agent over the Claude CLI backend, in the isolated mode. Each call
starts one process with a connection of its own, saves no session and gives
the model no tool. -/
def cli (name instructions : String) (model : String := "") : Agent :=
  { name, backend := Cli.backend model (isolated := true), instructions }

/-- Sends the instructions of the agent, followed by `input`, and returns the
reply. The input must be nonempty. -/
def ask (a : Agent) (input : String) : IO String := do
  ensure (!input.isEmpty) "the input of the agent is empty"
  a.backend.ask s!"{a.instructions}\n\n{input}"

/-- The agent reads the thread and adds its reply as one turn. Returns the
reply and the extended thread. The thread must be nonempty. The name of the
agent must be nonempty and must fit on one line. -/
def reply (a : Agent) (t : Thread) : IO (String × Thread) := do
  ensure (!a.name.isEmpty && !a.name.contains '\n') "the name of the agent is empty or spans lines"
  ensure (!t.isEmpty) "the thread is empty"
  let text := (← a.ask t.render).trimAscii.toString
  return (text, t.push { speaker := a.name, text })

end Agent

/-- A pair of adversarial agents. The proponent makes a proposal. The opponent
attacks it. -/
structure Pair where
  proponent : Agent
  opponent : Agent

/-- The result of a debate. -/
structure Debate where
  /-- The thread, with the turns of the debate. -/
  thread : Thread
  /-- The last reply of the proponent. -/
  proposal : String
  /-- Whether the check accepted the last proposal. -/
  accepted : Bool
  /-- The number of rounds that ran. -/
  rounds : Nat

/-- Runs a debate of the pair on the thread `t`. In each round the proponent
replies, the check judges the reply, and the opponent replies. The check
returns its verdict and an optional turn that reports it on the thread. The
debate ends when the check accepts the proposal and the opponent yields, or
after `rounds` rounds.

The number of rounds must be positive. The two agents must have distinct names. -/
def Pair.debate (p : Pair) (t : Thread) (rounds : Nat)
    (yields : String → Bool := fun _ => false)
    (check : String → IO (Bool × Option Turn) := fun _ => pure (true, none)) : IO Debate := do
  ensure (rounds > 0) "the debate has no round"
  ensure (p.proponent.name != p.opponent.name) "the two agents of the pair share a name"
  let mut thread := t
  let mut proposal := ""
  let mut accepted := false
  let mut ran := 0
  for _ in [0:rounds] do
    let (text, proposed) ← p.proponent.reply thread
    proposal := text
    let (ok, report) ← check text
    accepted := ok
    let checked := match report with
      | some turn => proposed.push turn
      | none => proposed
    let (answer, answered) ← p.opponent.reply checked
    thread := answered
    ran := ran + 1
    if ok && yields answer then break
  return { thread, proposal, accepted, rounds := ran }

end Adversarial
