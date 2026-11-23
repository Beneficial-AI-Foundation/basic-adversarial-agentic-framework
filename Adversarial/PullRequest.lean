import Adversarial.Agent

/-! The pull request flow for a mathematical issue.

An `Issue` is prose with mathematics. One adversarial pair creates the pull
request, which carries Lean code. A second adversarial pair reviews it. A
supervisor agent repeats both phases until it decides. The Lean checker judges
each version of the code.

A `Team` holds the five agents with their instructions. The function
`proveClaims` runs the flow on a file of issues and saves the results. -/

namespace Adversarial

open AIBackend

/-- Whether `pattern` occurs in `s`. -/
private def has (s pattern : String) : Bool := (s.splitOn pattern).length > 1

/-- A mathematical issue. Its text is prose with mathematics. The pull request
must prove a Lean theorem with the name `theoremName`. Whether the statement
of that theorem matches the prose is a question for the agents. -/
structure Issue where
  number : Nat
  title : String
  text : String
  theoremName : String

inductive Status where
  | merged
  | rejected
  /-- The supervisor reached no decision within the round limit. -/
  | undecided
deriving BEq, Repr

/-- The end of a pull request flow. -/
structure Outcome where
  status : Status
  /-- The last Lean code of the pull request. -/
  code : String
  /-- The number of rounds of the supervisor. -/
  rounds : Nat
  /-- The last reply of the supervisor. -/
  verdict : String
  thread : Thread

/-- The texts that the Lean code may not contain. They are the commands that run
code or extend the language. The list is a filter, not a sandbox. -/
def defaultForbidden : List String :=
  ["#eval", "#exit", "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab", "initialize",
   "unsafe", "@[extern", "implemented_by", "macro", "syntax", "elab ", "IO.",
   "set_option"]

/-- The axioms that a proof may depend on. -/
def defaultAllowedAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-- The name of a status in a report. -/
def Status.name : Status → String
  | .merged => "merged"
  | .rejected => "rejected"
  | .undecided => "undecided"

/-- The configuration of the Lean check. The default runs `lean --stdin`, so
the code may use the Lean core library only. A project with dependencies sets
`cmd` and `args`, for instance to `lake env lean --stdin`, and a `header` of
imports that precedes the code. -/
structure Checker where
  cmd : String := "lean"
  args : Array String := #["--stdin"]
  /-- The text that precedes the code, such as import lines. -/
  header : String := ""
  forbidden : List String := defaultForbidden
  allowedAxioms : List String := defaultAllowedAxioms
  /-- The time limit of one check, in milliseconds. -/
  timeoutMs : Nat := 300000

/-- The Lean check of the code of a pull request. It returns the reason of a
failure, or `none` when the code passes. The Lean checker elaborates the code
and prints the axioms of the theorem `name`. The check does not compare the
statement with the prose of the issue.

The name must consist of letters, digits and underscores, since it becomes
part of a Lean command. -/
def leanCheck (name code : String) (checker : Checker := {}) : IO (Option String) := do
  ensure (!name.isEmpty && name.all fun c => c.isAlphanum || c == '_')
    "the theorem name is not a plain identifier"
  if let some text := checker.forbidden.find? (has code ·) then
    return some s!"the code contains the forbidden text {text}"
  if (code.splitOn "\n").any (·.trimAsciiStart.toString.startsWith "import ") then
    return some "the code contains an import command"
  let source := s!"{checker.header}{code}\n#print axioms {name}\n"
  let out ← try
      runProcessOutput checker.cmd checker.args (some source) checker.timeoutMs
    catch e => return some s!"the Lean check did not run to its end. {e}"
  if out.exitCode != 0 then return some s!"Lean rejects the code. {out.stdout}"
  if has out.stdout s!"'{name}' does not depend on any axioms" then return none
  match out.stdout.splitOn s!"'{name}' depends on axioms: [" with
  | [_, rest] =>
    let axioms := ((rest.splitOn "]").headD "").splitOn ", "
    match axioms.find? (!checker.allowedAxioms.contains ·) with
    | some a => return some s!"the proof depends on the axiom {a}"
    | none => return none
  | _ => return some "Lean printed no axiom report for the theorem"

/-- The content of a reply without a surrounding Markdown fence. -/
def stripFence (reply : String) : String :=
  match reply.trimAscii.toString.splitOn "\n" with
  | first :: rest =>
    if first.startsWith "```" then "\n".intercalate (rest.takeWhile (!·.startsWith "```"))
    else "\n".intercalate (first :: rest)
  | [] => ""

/-- Runs the pull request flow of an issue.

Each round of the supervisor has three phases. In the first phase the pair
`authors` creates the pull request. Its proponent writes the code. The Lean
check reports on the thread. Its opponent attacks the code. The phase ends
when the check passes and the opponent has no objection, or after
`pairRounds` rounds. In the second phase the pair `reviewers` debates the
code once. In the third phase the supervisor reads the thread and decides.

The first word of the supervisor's reply is the decision, without punctuation
or emphasis marks. `MERGE` ends the
flow when the Lean check accepted the last version of the code. Otherwise the flow reports
the refusal on the thread and continues. `REJECT` ends the flow. `REVISE`
starts the next round. The flow raises an `IO` error on any other reply. It
ends with the status `undecided` when the supervisor reaches no decision
within `maxRounds` rounds. -/
def pullRequestFlow (authors reviewers : Pair) (supervisor : Agent) (issue : Issue)
    (maxRounds : Nat := 4) (pairRounds : Nat := 3) (checker : Checker := {}) : IO Outcome := do
  let mut thread : Thread := #[{
    speaker := "issue"
    text := s!"Issue #{issue.number}. {issue.title}\n{issue.text}\n" ++
      s!"The main theorem of the code must have the name {issue.theoremName}." }]
  let mut code := ""
  let mut verdict := ""
  for round in [1:maxRounds + 1] do
    let creation ← authors.debate thread pairRounds (·.startsWith "NO OBJECTION") fun reply => do
      match ← leanCheck issue.theoremName (stripFence reply) checker with
      | none => pure (true, some { speaker := "lean", text := "Lean accepts the code." })
      | some failure =>
        pure (false, some { speaker := "lean", text := s!"The Lean check failed. {failure}" })
    let review ← reviewers.debate creation.thread 1
    let (reply, decided) ← supervisor.reply review.thread
    thread := decided
    verdict := reply
    code := stripFence creation.proposal
    let decision := String.ofList ((verdict.toList.dropWhile (!·.isAlpha)).takeWhile Char.isAlpha)
    if decision == "MERGE" then
      if creation.accepted then
        return { status := .merged, code, rounds := round, verdict, thread }
      thread := thread.push ⟨"lean",
        "The merge did not happen, since the Lean check of the last version of the code failed."⟩
    else if decision == "REJECT" then
      return { status := .rejected, code, rounds := round, verdict, thread }
    else if decision != "REVISE" then
      throw (IO.userError s!"the reply of the supervisor is outside the protocol: {verdict}")
  return { status := .undecided, code, rounds := maxRounds, verdict, thread }

/-! ## Teams -/

/-- The rules that every agent of a team receives. -/
def houseRules : String :=
  "You take part in a pull request for a Lean 4 project that uses the Lean core library " ++
  "only, without Mathlib. The thread below starts with an issue in prose. Each later turn " ++
  "has a header line with the name of its speaker. The speaker lean reports the result of " ++
  "the Lean checker. "

/-- The five agents of a pull request flow. -/
structure Team where
  authors : Pair
  reviewers : Pair
  supervisor : Agent

namespace Team

/-- Builds a team. The function `make` builds each agent from its name and its
instructions, with a connection of its own. -/
def make (make : String → String → IO Agent) : IO Team := do
  -- Each adversary has a fixed position and no option to agree at once. The
  -- challenger and the critic must attack, and the defender must rebut.
  let authors : Pair := {
    proponent := ← make "prover" (houseRules ++
      "You are the prover. Reply with the complete Lean 4 code and nothing else, with no " ++
      "Markdown fence. State the claim of the issue faithfully as the theorem with the " ++
      "required name, preceded by a docstring. Use no sorry, no new axiom, no import and no " ++
      "command that runs code. When the thread holds an objection, a defect or a direction, " ++
      "either repair the code or answer in a Lean comment at the top of the code why the " ++
      "point does not hold.")
    opponent := ← make "challenger" (houseRules ++
      "You are the challenger, the adversary of the prover. Your task is to make the pull " ++
      "request fail. In each turn state the strongest objection to the last code that you " ++
      "can defend. Examine whether the Lean statement says exactly what the prose of the " ++
      "issue says, whether an encoding of a mathematical object needs a proof of its " ++
      "faithfulness, whether a hypothesis is vacuous or missing, whether the claim is " ++
      "weaker, stronger or the negation of the prose, and whether the Lean check failed. " ++
      "Reply OBJECTION followed by the objection in at most four sentences. Never reply NO " ++
      "OBJECTION in your first turn. Reply NO OBJECTION in a later turn only when the " ++
      "prover answered every objection of yours and you can defend no further one.") }
  let reviewers : Pair := {
    proponent := ← make "critic" (houseRules ++
      "You are the critic, a reviewer whose position is that the pull request must not " ++
      "merge. Present the strongest case for that position in at most three numbered " ++
      "points. Judge the last code with respect to the prose of the issue, and judge " ++
      "whether the prover answered the challenger. You may not agree with the merge.")
    opponent := ← make "defender" (houseRules ++
      "You are the defender, a reviewer whose position is that the pull request must merge, " ++
      "and the adversary of the critic. Rebut each point of the critic in at most two " ++
      "sentences per point. Concede a point only when you cannot rebut it.") }
  let supervisor ← make "supervisor" (houseRules ++
    "You are the supervisor. The challenger and the critic must attack by their role, and " ++
    "the defender must rebut by its role, so weigh the substance of each point and not the " ++
    "position. The first word of your reply is MERGE, REVISE or REJECT, followed by at most " ++
    "three sentences. Reply MERGE only when Lean accepts the last code, its statement " ++
    "matches the issue and no point of the critic stands. Reply REJECT when the claim of the " ++
    "issue is false, even when the code proves its negation. Otherwise reply REVISE with " ++
    "directions for the prover.")
  return { authors, reviewers, supervisor }

/-- A team over the Claude API backend. Each agent has a client of its own,
hence a connection of its own. The thinking of the model counts toward
`maxTokens`, and a long proof needs room after it. -/
def api (maxTokens : Nat := 32000) : IO Team :=
  make fun name instructions => Agent.apiOwn name instructions (maxTokens := maxTokens)

/-- A team over the Claude CLI backend. Each call of an agent is one isolated process. -/
def cli : IO Team :=
  make fun name instructions => pure (Agent.cli name instructions)

/-- Runs the pull request flow of an issue with this team. -/
def run (team : Team) (issue : Issue) (maxRounds : Nat := 4) (pairRounds : Nat := 3)
    (checker : Checker := {}) : IO Outcome :=
  pullRequestFlow team.authors team.reviewers team.supervisor issue maxRounds pairRounds checker

end Team

/-! ## Claims -/

/-- Reads issues from a JSON file. The file holds an array of objects with the
fields `number`, `title`, `text` and `theoremName`. Further fields, such as
the source of a claim, are ignored. -/
def loadIssues (path : System.FilePath) : IO (List Issue) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let items ← IO.ofExcept json.getArr?
  items.toList.mapM fun item => IO.ofExcept do
    return {
      number := ← item.getObjValAs? Nat "number"
      title := ← item.getObjValAs? String "title"
      text := ← item.getObjValAs? String "text"
      theoremName := ← item.getObjValAs? String "theoremName" }

/-- Runs the pull request flow on a list of issues. The action `team` builds
a new team for each issue, so no issue shares a connection with another one.
The directory `results` receives, per issue, the thread of the flow and the
accepted Lean code, and a summary under the name of `label`. The value `only`
restricts the run to one issue by number. The run skips an issue whose thread
file exists, so an interrupted run resumes.

The function returns the number of issues whose flow raised an error. -/
def proveIssues (team : IO Team) (label : String) (issues : List Issue)
    (results : System.FilePath) (only : Option Nat := none) (checker : Checker := {}) : IO Nat := do
  ensure (!label.isEmpty && label.all fun c => c.isAlphanum || c == '_')
    "the label is not a plain identifier"
  IO.FS.createDirAll results
  let mut errors := 0
  for issue in issues do
    let done ← (results / s!"{issue.theoremName}.thread.md").pathExists
    if only.all (· == issue.number) && !done then
      ensure (!issue.theoremName.isEmpty && issue.theoremName.all fun c => c.isAlphanum || c == '_')
        s!"the theorem name of issue {issue.number} is not a plain identifier"
      let start ← IO.monoMsNow
      let outcome ← (do (← team).run issue (checker := checker)).toBaseIO
      let seconds := ((← IO.monoMsNow) - start) / 1000
      let row ← match outcome with
        | .ok pr => do
          IO.FS.writeFile (results / s!"{issue.theoremName}.thread.md") pr.thread.render
          if pr.status == .merged then
            IO.FS.writeFile (results / s!"{issue.theoremName}.lean") (pr.code ++ "\n")
          let objections := (pr.thread.turnsOf "challenger").filter (·.startsWith "OBJECTION")
          pure s!"| {issue.number} | {issue.title} | {pr.status.name} | {pr.rounds} | {objections.length} | {seconds} |"
        | .error e => do
          errors := errors + 1
          IO.eprintln s!"issue {issue.number}: {e}"
          pure s!"| {issue.number} | {issue.title} | error | | | {seconds} |"
      IO.println row
      let summary := results / s!"summary-{label}.md"
      unless ← summary.pathExists do
        IO.FS.writeFile summary
          "| Issue | Title | Status | Supervisor rounds | Objections of the challenger | Seconds |\n| --- | --- | --- | --- | --- | --- |\n"
      let handle ← IO.FS.Handle.mk summary .append
      handle.putStrLn row
  return errors

/-- Runs `proveIssues` on the issues of a JSON file. The results go to the
directory `results` beside the file. -/
def proveClaims (team : IO Team) (label : String) (path : System.FilePath)
    (only : Option Nat := none) (checker : Checker := {}) : IO Nat := do
  proveIssues team label (← loadIssues path) ((path.parent.getD ".") / "results") only checker

end Adversarial
