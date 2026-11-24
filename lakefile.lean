import Lake
open System Lake DSL

package adversarial

/-- The backends. The package `aibackend` provides the Claude API client, the
Claude CLI backend, the key handling and the TLS checks. -/
require aibackend from git
  "https://github.com/Beneficial-AI-Foundation/lean-aibackend.git" @ "main"

/-- The link arguments of libcurl. Lake passes the static C shim of
`aibackend` on to this package, but not its link arguments, so this file
repeats them. Lean's bundled linker does not search the macOS SDK. -/
def curlLinkArgs : Array String :=
  if Platform.isOSX then
    #["-L", run_io do
      let out ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      return out.stdout.trimAscii.toString ++ "/usr/lib", "-lcurl"]
  else #["-lcurl"]

lean_lib Adversarial

/-- Runs the pull request flow on the claims of a JSON file. -/
@[default_target]
lean_exe prove where
  root := `Prove
  moreLinkArgs := curlLinkArgs

/-- The application scenarios, with the simulated assistants of `tests/mock_server.py`. -/
lean_exe scenarios where
  root := `Scenarios
  srcDir := "tests"
  moreLinkArgs := curlLinkArgs

/-- The test driver. It builds and runs the executable `scenarios`. -/
@[test_driver]
script test args do
  let child ← IO.Process.spawn { cmd := (← getLake).toString, args := #["exe", "scenarios"] ++ args.toArray }
  child.wait
