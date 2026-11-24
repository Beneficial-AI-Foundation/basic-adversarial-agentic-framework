import Adversarial

open Adversarial

/-- Runs the pull request flow with five real Claude agents per issue.

Usage: `prove <source> [ffi|cli] [number|all] [maxTokens]`. The source is the
word `examples`, for the example issues of `Adversarial.Examples`, or the path
of a JSON file of issues. The backend is `ffi` by default. That backend needs
an Anthropic API key in the secret store, and `prove` reads the key once
before the first issue. Without a key it stops with a message that names the
backend `cli`. A number restricts
the run to one issue. The last argument sets the token limit of a reply over
the API backend, which is 64000 by default.

The results of the examples go to `examples/results`, and the results of a
file go to the directory `results` beside it. A run over the API backend also
adds one record per call of an agent to the file `usage-ffi.md` there. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | source :: rest =>
    let backend := rest.headD "ffi"
    unless backend == "ffi" || backend == "cli" do
      IO.eprintln s!"unknown backend {backend}, expected ffi or cli"
      return 1
    if backend == "ffi" then
      if let .error e ← (AIBackend.Claude.Api.Client.fromDefault).toBaseIO then
        IO.eprintln s!"The ffi backend found no Anthropic API key. {e}
Store the key once with
  security add-generic-password -a \"$USER\" -s lean-aibackend-anthropic-api-key -w
or run the logged in claude CLI instead, with the backend cli, as in
  lake exe prove {source} cli"
        return 1
    let only := ((rest.drop 1).head?).bind (·.toNat?)
    let maxTokens := (((rest.drop 2).head?).bind (·.toNat?)).getD 64000
    let issues ← if source == "examples" then pure (Examples.all.map (·.issue)) else loadIssues source
    let results : System.FilePath :=
      if source == "examples" then "examples" / "results"
      else ((System.FilePath.mk source).parent.getD ".") / "results"
    IO.FS.createDirAll results
    let usageLog := results / "usage-ffi.md"
    if backend == "ffi" then
      unless ← usageLog.pathExists do IO.FS.writeFile usageLog Agent.usageHeader
    let team (issue : Issue) : IO Team :=
      if backend == "cli" then Team.cli
      else Team.api maxTokens (some usageLog) (toString issue.number)
    let errors ← proveIssues team backend issues results only
    return (if errors == 0 then 0 else 1)
  | [] =>
    IO.eprintln "usage: prove <examples | issues.json> [ffi|cli] [number|all] [maxTokens]"
    return 1
