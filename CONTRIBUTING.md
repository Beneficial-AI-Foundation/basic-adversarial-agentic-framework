# Contributing to Adversarial Agents

Thanks for your interest in contributing. This is a Lean 4 command-line
framework that runs a pull-request flow with several real Claude agents per
issue, built on
[Lean AI Backend](https://github.com/Beneficial-AI-Foundation/lean-aibackend).
This guide covers how to build it, test it, and send a change. It follows the
shared contribution standard used across the
[Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation) Lean
projects.

## Platform

The package **works on macOS** (Apple silicon). Linux and Windows are work in
progress, because the `lean-aibackend` dependency fails to link on Linux today
(Lean's bundled linker does not search the system libcurl) and Windows has no
default key helper. Continuous integration builds and runs the scenarios on
macOS.

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project
uses, so you don't install Lean by hand:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Because this package links the `lean-aibackend` C shim, building also needs, on
macOS (the Command Line Tools for Xcode provide all but `elan`):

- a C compiler and **libcurl 7.85.0 or later**, with TLS support and
  `curl-config`.

Running the real pull-request flow (`lake exe prove … ffi`) additionally needs an
Anthropic API key in the operating-system secret store, or the logged-in
`claude` CLI (`… cli`).

## Building and testing

```sh
lake build prove scenarios   # build the CLI and the scenario runner
lake test                    # run the scenarios against the simulated assistants
```

`lake test` fetches `lean-aibackend`, builds the package and runs the scenarios
with the simulated assistants of `tests/mock_server.py`. **It needs no API key
and spends no tokens.**

Running the agents for real spends tokens:

```sh
lake exe prove examples cli        # the example issues, through the Claude CLI
lake exe prove book/claims.json    # the claims of the book, through the API backend
```

Continuous integration builds the CLI and runs the scenarios on macOS for every
push and pull request (see `.github/workflows/ci.yml`). It does **not** run
`prove`, because that spends tokens and needs credentials. Please make sure the
build and the scenarios pass locally before opening a PR.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a scenario for behaviour
   you change.
3. Make sure `lake build prove scenarios` and `lake test` pass, and that CI is
   green.
4. Write a clear PR description: what changed, why, and how you verified it. If
   you ran the agents for real, do not paste keys or raw token-usage secrets.
5. By contributing, you agree your contribution is licensed under this
   repository's license (see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits
   (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest issue file or command that reproduces it. Security-sensitive reports can
be sent privately to **support@beneficialaifoundation.org** instead of a public
issue. Never paste an API key into an issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers
may remove comments, commits or contributions that don't meet this standard.
