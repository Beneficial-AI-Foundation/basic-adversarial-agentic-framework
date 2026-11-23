import Adversarial

open Adversarial

/-- Runs the pull request flow with five real Claude agents per issue.

Usage: `prove <source> [ffi|cli] [number]`. The source is the word `examples`,
for the example issues of `Adversarial.Examples`, or the path of a JSON file
of issues. The backend is `ffi` by default. The number restricts the run to
one issue. The results of the examples go to `examples/results`, and the
results of a file go to the directory `results` beside it. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | source :: rest =>
    let backend := rest.headD "ffi"
    unless backend == "ffi" || backend == "cli" do
      IO.eprintln s!"unknown backend {backend}, expected ffi or cli"
      return 1
    let only := ((rest.drop 1).head?).bind (·.toNat?)
    let team := if backend == "cli" then Team.cli else Team.api
    let errors ←
      if source == "examples" then
        proveIssues team backend (Examples.all.map (·.issue)) ("examples" / "results") only
      else
        proveClaims team backend source only
    return (if errors == 0 then 0 else 1)
  | [] =>
    IO.eprintln "usage: prove <examples | issues.json> [ffi|cli] [number]"
    return 1
