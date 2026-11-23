# basic-adversarial-agentic-framework

A Lean 4 package of adversarial Claude agents. Two pairs of agents with
opposed roles create and review a pull request that carries Lean code for a
mathematical issue in prose. A supervisor agent repeats both phases until it
decides. The Lean checker judges each version of the code.

The package builds on [lean-aibackend](https://github.com/Beneficial-AI-Foundation/lean-aibackend),
which provides the Claude API client, the Claude CLI backend, the key handling
and the TLS checks.

**Platforms.** The package works on macOS. Linux and Windows are work in
progress, since the build of `lean-aibackend` fails on Linux at the link step
today, and Windows has no default key helper there.

The repository is `basic-adversarial-agentic-framework`, the Lake package is
`adversarial`, and the library to import is `Adversarial`.

## Installation

The package needs the tools of `lean-aibackend`, which its README lists. They
are `elan`, a C compiler, the libcurl library with its headers, `python3` and
`openssl`. The scenarios also run `lean`, which `elan` provides.

```
git clone https://github.com/Beneficial-AI-Foundation/basic-adversarial-agentic-framework.git
cd basic-adversarial-agentic-framework
lake test
```

The command `lake test` fetches `lean-aibackend`, builds the package and runs
the scenarios with simulated assistants. It needs no API key and no Claude
CLI.

A run with real agents needs one of the two Claude backends.

| Backend | Requirement |
| --- | --- |
| `ffi` | An Anthropic API key in the secret store. On macOS the command `security add-generic-password -a "$USER" -s lean-aibackend-anthropic-api-key -w` stores it. |
| `cli` | The `claude` CLI, already logged in |

## Quick start

The executable `prove` runs the flow with five real Claude agents per issue.

```
lake exe prove examples ffi 12        # one example issue, through the API
lake exe prove examples cli 12        # the same issue, through the Claude CLI
lake exe prove examples               # every example issue
lake exe prove book/claims.json       # the claims of the book
lake exe prove <issues.json> [ffi|cli] [number|all] [maxTokens]
```

A run prints one row per issue and writes three kinds of files.

| File | Content |
| --- | --- |
| `<name>.lean` | The Lean code that the supervisor accepted |
| `<name>.thread.md` | The whole discussion of the five agents |
| `summary-<backend>.md` | One row per issue, with the status, the supervisor rounds and the objections |
| `usage-ffi.md` | One record per call of an agent over the API backend, with its output tokens, its stop reason and its duration |

The results of the examples go to `examples/results`. The results of a file
go to the directory `results` beside it. A run skips an issue whose thread
file exists, so an interrupted run resumes. A run with real agents spends
tokens.

A file of issues is a JSON array. Each issue has the fields `number`, `title`,
`text` and `theoremName`. The text is prose with mathematics. The theorem name
consists of letters, digits and underscores.

## Agents

The module `Adversarial.Agent` holds the agents.

| Declaration | Role |
| --- | --- |
| `Agent` | A Claude backend with a name and standing instructions |
| `Agent.apiOwn name instructions` | An agent over the API backend with a client of its own, hence a connection of its own |
| `Agent.api c name instructions` | An agent over the API backend that uses the connection of the client `c` |
| `Agent.cli name instructions` | An agent over the CLI backend, where each call is one isolated process |
| `Thread`, `Turn` | The conversation that several agents share, with one header line per turn |
| `Agent.reply` | The agent reads the thread and adds one turn |
| `Pair` | Two adversarial agents, a proponent and an opponent |
| `Pair.debate` | Rounds of proposal, optional check and attack, until the check accepts the proposal and the opponent yields |

Agents share no connection. Each `Agent.apiOwn` agent owns one client. Each
call of an `Agent.cli` agent starts one `claude -p` process with the options
`--no-session-persistence` and `--tools ""`. The process saves no session, and
the model has no tool, so it can neither read nor write a file or a memory.
The thread is the only channel between agents.

The function `Thread.render` gives a leading space to any line of a turn that
starts like a header. A turn therefore cannot forge the header of another
speaker.

## Pull request flow

The module `Adversarial.PullRequest` holds the flow. An issue is prose with
mathematics. It fixes only the name of the Lean theorem. Five agents take
part.

| Agent | Pair | Role |
| --- | --- | --- |
| prover | authors, proponent | Writes the Lean code |
| challenger | authors, opponent | States its strongest objection to the code, for instance a statement that differs from the prose |
| critic | reviewers, proponent | Argues that the code must not be accepted |
| defender | reviewers, opponent | Rebuts the critic |
| supervisor | none | Reads the thread and replies `MERGE`, `REVISE` or `REJECT` |

Each round of the supervisor has three phases.

1. The authors debate. After each version of the code the Lean checker reports
   on the thread. It refuses `sorry`, a new axiom, an import and the commands
   that run code. The phase ends when the check passes and the challenger has
   no objection.
2. The reviewers debate the code once.
3. The supervisor decides. `REVISE` starts the next round. `MERGE` takes
   effect only when the Lean check accepted the last version of the code. The
   flow ends with the status `undecided` after four rounds.

The status `merged` records the decision `MERGE` of the supervisor. The flow
performs no git operation. It writes the accepted code to a file.

The Lean check does not compare the statement with the prose. That comparison
is the task of the challenger, of the reviewers and of the supervisor. An
accepted file is therefore a proof that Lean checked, of a statement that
agents judged faithful. No person reviewed that judgment.

| Declaration | Role |
| --- | --- |
| `Issue` | Prose with mathematics, and the name of the Lean theorem |
| `Checker`, `leanCheck` | The Lean check. The default runs `lean --stdin`, with a time limit of 300 seconds, so the code uses the Lean core library only |
| `pullRequestFlow` | The flow, for two pairs and a supervisor |
| `Team`, `Team.api`, `Team.cli` | The five agents with their instructions, over the API backend or the CLI backend |
| `Team.run` | The flow of one issue with a team |
| `proveIssues`, `proveClaims`, `loadIssues` | The flow on a list of issues or on a JSON file, with saved results |

A program calls the flow like this.

```lean
import Adversarial
open Adversarial

def main : IO Unit := do
  let issue : Issue := {
    number := 1
    title := "The sum of two even numbers is even"
    text := "A natural number n is even when n = 2k for some natural number k. " ++
      "Prove that the sum of two even natural numbers is even."
    theoremName := "even_add_even" }
  let outcome ← (← Team.api).run issue
  IO.println s!"{outcome.status.name} after {outcome.rounds} rounds\n{outcome.code}"
```

## Example issues

The module `Adversarial.Examples` holds eleven issues. Two claims are false,
so a correct flow ends them with a rejection.

| Number | Issue | Claim |
| --- | --- | --- |
| 12 | The sum of two even numbers is even | true |
| 15 | n + 1 = n for every natural number n | false |
| 21 | No rational number has square 2 | true |
| 22 | For every natural number n there is a prime p with p > n | true |
| 23 | n² + n + 41 is prime for every natural number n | false, at n = 40 |
| 24 | Among six people, three all know one another or three are mutual strangers | true |
| 25 | Every natural number n ≥ 2 has a factorization into primes, unique up to order | true |
| 26 | Fermat's little theorem | true |
| 27 | x² + y² ≥ 2xy for all real numbers, with equality exactly when x = y | true |
| 28 | The pigeonhole principle | true |
| 29 | Every non-increasing sequence of natural numbers is eventually constant | true |

Issues 12, 21, 22, 23, 24 and 27 ran with real agents during the development
of the package. Issues 25, 26, 28 and 29 have not run.

## The book

The directory `book` holds a larger example. Its claims are 18 propositions of
H. S. Hall and S. R. Knight, "Higher Algebra", Fourth Edition, Macmillan,
1891. The scan is at https://archive.org/details/higheralgebraseq00hall. The
book is in the public domain in the United States by its date of publication.
The file `book/source.json` records the source.

The file `book/claims.json` holds the claims. The text of each claim is the
text that the book prints, with its article number. An agent typed each
statement from a page image of the scan. Two of the 18, Art. 40 and Art. 111,
have a second comparison with the page images. Five claims record, in the
field `gaps`, a condition that the book does not print, such as r ≠ 1 in
Art. 55. The agents do not see that field.

The directory `book/results` holds the results of two runs through the API
backend. The first run used a limit of 32000 tokens per reply. The second run
repeated the three claims that ended with an error, with a limit of 64000.

| Art. | Topic | Status | Supervisor rounds | Objections of the challenger |
| --- | --- | --- | --- | --- |
| 40 | Sum of an arithmetical progression | merged | 3 | 2 |
| 55 | Sum of a geometrical progression | merged | 1 | 1 |
| 57 | Sum to infinity of a geometrical progression | merged | 2 | 2 |
| 65 | The relation AH = G² between the three means | merged | 1 | 1 |
| 68 | Sum of the squares of the first n natural numbers | merged | 2 | 2 |
| 69 | Sum of the cubes of the first n natural numbers | merged | 1 | 1 |
| 111 | Solution of the quadratic equation | merged | 1 | 1 |
| 113 | Nature of the roots of the quadratic equation | merged, in the second run | 3 | 4 |
| 114 | Sum and product of the roots | merged | 2 | 2 |
| 163 | Binomial theorem for a positive integral index | merged | 1 | 2 |
| 204 | Logarithm of a product | merged | 1 | 1 |
| 205 | Logarithm of a fraction | merged | 2 | 2 |
| 206 | Logarithm of a power | merged | 1 | 2 |
| 246 | Properties of an inequality | merged | 2 | 1 |
| 250 | Arithmetic and geometric mean of two quantities | merged, in the second run | 3 | 2 |
| 253 Cor. | Arithmetic and geometric mean of n quantities | error, in both runs | | |
| 514 | Remainder of a division by x − a | merged | 1 | 1 |
| 514 Cor. | Its corollary | merged | 2 | 3 |

### The token limit and the second run

In the first run three claims ended with an error. Each time a reply of an
agent reached the limit of 32000 tokens, and the client raises an error on an
incomplete reply. The output tokens of a reply include the thinking of the
model.

The second run repeated those three claims with a limit of 64000 tokens. The
choice of that value rests on two measurements of the second run itself, which
recorded each call of an agent in `book/results/usage-ffi.md`.

1. The need. Five of the 16 replies of the prover held more than 32000 tokens.
   The largest complete reply held 51100.
2. The ceiling. The client does not stream, and a request ends after 600
   seconds. The long replies of the prover arrived at 108 to 156 tokens per
   second, and at 121 on average. A reply of 64000 tokens took 549 seconds.
   The limit of 64000 is therefore the largest round value that fits in one
   request.

| Claim | Result of the second run | Largest reply of the prover |
| --- | --- | --- |
| Art. 113 | merged in the third supervisor round | 51100 tokens |
| Art. 250 | merged in the third supervisor round | 29744 tokens |
| Art. 253 Cor. | error. The third reply of the prover reached 64000 tokens after 549 seconds | 64000 tokens, incomplete |

Art. 253 Cor. remains without a result. A higher limit cannot help with the
present client, since a larger reply exceeds the request limit of 600 seconds.
The claim needs a client that streams, a longer request limit or shorter
replies. Its first run with the old limit of 32000 failed for the same reason,
and so did Art. 250, whose largest reply came just under that old limit in the
second run.

### Token usage of the second run

The run made 49 requests, all with HTTP status 200. It produced 435705 output
tokens in 3722 seconds of request time. The records hold output tokens only.
The first run wrote no usage records.

| Agent | Calls | Output tokens | Share | Largest reply | Mean reply | Tokens per second |
| --- | --- | --- | --- | --- | --- | --- |
| prover | 16 | 393081 | 90.2 % | 64000 | 24567 | 121 |
| challenger | 15 | 14259 | 3.3 % | 1847 | 950 | 85 |
| critic | 6 | 14096 | 3.2 % | 3174 | 2349 | 94 |
| defender | 6 | 9112 | 2.1 % | 2144 | 1518 | 92 |
| supervisor | 6 | 5157 | 1.2 % | 1027 | 859 | 83 |

| Claim | Calls | Output tokens | Request seconds | Tokens of the prover |
| --- | --- | --- | --- | --- |
| Art. 113 | 23 | 224201 | 1879 | 203938 in 7 replies |
| Art. 250 | 21 | 87471 | 785 | 66235 in 6 replies |
| Art. 253 Cor. | 5 | 124033 | 1058 | 122908 in 3 replies |

The prover produced nine tenths of the output tokens. Every other agent
stayed below 3200 tokens per reply.

### Fidelity of the accepted statements

Several accepted statements are abstract, since the Lean core library has no
real numbers. Art. 113 and Art. 250 hold over a field with an order that the
file itself defines. Art. 111 holds over a field, with the hypotheses a ≠ 0 and
2 ≠ 0. Art. 204 holds for any operation with three assumed laws of a power.
Art. 57 states the sum to infinity through an inequality on integers. The
fidelity of each encoding rests on the judgment of the agents.

The test suite checks that each of the 17 accepted files still passes the
Lean check.

## Use from another Lake project

Another project requires the package in its `lakefile.lean`. Lake passes the
C shim of `lean-aibackend` on, but not the libcurl link arguments, so each
executable repeats them.

```lean
require adversarial from git
  "https://github.com/Beneficial-AI-Foundation/basic-adversarial-agentic-framework.git" @ "main"

def curlLinkArgs : Array String :=
  if Platform.isOSX then
    #["-L", run_io do
      let out ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      return out.stdout.trimAscii.toString ++ "/usr/lib", "-lcurl"]
  else #["-lcurl"]

lean_exe myapp where
  root := `MyApp
  moreLinkArgs := curlLinkArgs
```

The agents over the API backend work in a compiled executable only, since
that backend uses native code. The agents over the CLI backend also work in
the interpreter.

This package names the toolchain v4.36.0. The accepted code of the book uses
declarations of that toolchain, such as `Lean.Grind.Field` and `Rat`.

## Tests

The command `lake test` runs six scenarios with the deterministic simulated
assistants of `tests/mock_server.py`, through the `Claude.Api` client and TLS.

| Scenario | Content |
| --- | --- |
| Pull requests | The flow with scripted agents. One issue merges in the second round, after an unfinished proof, a different statement and a vacuous hypothesis. A false issue ends with `REJECT`. Further cases cover a merge without a passing check, a supervisor outside the protocol, a forged header, the preconditions of a debate and the Lean check. Each scripted agent has a connection of its own, which the scenario verifies. |
| Calculator agent | A tool loop of an agent, on 150 generated tasks |
| Agent failures | The same loop with an unknown tool, wrong arguments, an endless assistant, a reply outside the protocol and a refusal |
| Tool use blocks | A tool loop over `tool_use` and `tool_result` blocks, with a forged history as the negative case |
| Parallel workers | Eight agents in parallel, each with its own client |
| Book | The 17 accepted Lean files of the book pass the Lean check |

The variable `AIBACKEND_LIVE` adds runs of the flow with five real Claude
agents, on the example issue whose number `AIBACKEND_ISSUE` holds. The value
`ffi` or `cli` selects one backend.

## Layout

- `Adversarial/Agent.lean` — agents, threads and adversarial pairs.
- `Adversarial/PullRequest.lean` — the flow, the Lean check, teams and the runs on issues.
- `Adversarial/Examples.lean` — the example issues.
- `Prove.lean` — the executable `prove`.
- `book/` — the claims of the book and the results of one run.
- `tests/Scenarios.lean` — the scenarios.
- `tests/mock_server.py` — the mock of the Messages API, with the simulated assistants.

## Limits

- The list of forbidden commands in the Lean check is a filter, not a sandbox.
  A run with real agents elaborates Lean source that a model wrote.
- The code of an issue uses the Lean core library only, since the default
  check runs without Mathlib.
- The flow has a limit of four supervisor rounds and of three rounds per
  debate of the authors.
- A reply of an agent over the API backend has a limit of 64000 tokens, which
  includes the thinking of the model. A larger reply does not fit in one
  request of 600 seconds, as the section on the token limit explains.

## License

The package is under the MIT license. See the file `LICENSE`.
