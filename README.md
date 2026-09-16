# mathlib-statistics-survey

This is a retrospective survey of probability and statistics in Mathlib. The core idea of this repository is reverse engineering. Given a current Lean file, can we write a design document to understand its design process?

Each document asks:

- What are the core mathematical theorems or structures that the file is trying to establish?
- What definitions did the authors need?
- Where is each assumption used?
- What are the possible connections between this file and other files?

## Project aims

1. **Write design documents.** Write a Markdown design document for every Lean file related to statistics or probability. [Invariance.md](Mathlib/Probability/Kernel/Invariance/Invariance.md) provides one example for [`Mathlib.Probability.Kernel.Invariance`](https://github.com/leanprover-community/mathlib4/blob/7d32461ad224e921eb05ead7ac02156702f4aa59/Mathlib/Probability/Kernel/Invariance.lean#L37-L40).

2. **Make Lean easier for statisticians to understand mathematically.** The goal is to make statisticians capable of reviewing Lean output by understanding its exact language and grammar.

3. **Understand the gaps and propose next steps.** We can look for small, direct pull requests that we could contribute to Mathlib, either by cleaning up the code or by proposing a more general solution. The book we currently want to compare with Mathlib is [*Foundations of Modern Probability*](https://link.springer.com/book/10.1007/978-3-030-61871-1).

## Using AI

Please use AI effectively, but remember that the goal of contributing to this project is to make things readable and clear.

You are encouraged to use Lean skills such as [lean4-skills](https://github.com/cameronfreer/lean4-skills) and [Lean skills](https://github.com/leanprover/skills). ChatGPT is also good at explaining and searching.

## Make a PR

One PR is expected to be a survey over one single LEAN file. 

An example can be found here in [EXAMPLE.md](EXAMPLE.md) against the file  [Invariance.lean](https://github.com/leanprover-community/mathlib4/blob/7d32461ad224e921eb05ead7ac02156702f4aa59/Mathlib/Probability/Kernel/Invariance.lean)

A template can be found in [TEMPLATE.md](TEMPLATE.md). - This is very initial, and we could make a better agreed template - comments are welcome!
