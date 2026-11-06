# MiniLean

MiniLean is an educational proof assistant implemented in Lean 4. Its purpose
is to make the main pieces of a proof assistant understandable by building
them incrementally: a small logic, a proof language, a trusted checker, a
parser, proof-search tools, and a growing library of formalized mathematics.

The project itself is written in Lean. Lean's kernel checks the MiniLean
implementation, while MiniLean's own checker validates proof terms in the
MiniLean language. This separation makes the project useful both as a Lean
programming project and as a way to study how proof assistants are structured.

> **Project status:** early prototype. The core syntax and first checker rules
> are present. The parser, interactive proof language, tactics, and larger
> theorem library are planned work.

## Goals

- Keep the trusted core small, explicit, and easy to audit.
- Make proof checking deterministic and executable.
- Explain every language feature with examples and documentation.
- Grow in independently understandable stages, with a working result at each
  stage.
- Use Lean's type system to state and prove properties about MiniLean itself.

## Current features

- Formula syntax for atomic propositions, falsehood, implication, conjunction,
  and disjunction.
- Proof-term syntax for assumptions, implication introduction and elimination,
  conjunction introduction and projections, disjunction introduction and
  elimination, and elimination from falsehood.
- A recursive checker that infers the conclusion of a proof term or rejects
  the term with `none`.
- A `check` function that accepts a proof only when its inferred conclusion
  matches the requested theorem.
- Example proof terms for identity, modus ponens, and conjunction swapping.

## Quick start

Install Lean 4 and Lake through [Elan](https://lean-lang.org/install/). The
toolchain is pinned in `lean-toolchain` so contributors use the same Lean
version.

From the repository root, build and run the executable:

```sh
lake build
lake exe minilean
```

The examples in `MiniLean/Examples.lean` also contain `#eval` commands that
evaluate representative proof checks during compilation.

## A first example

Formulas and proof terms are currently written directly as Lean values. This
proof constructs `P → P` by introducing `P` as an assumption and then using
that assumption:

```lean
open MiniLean

def p : Formula := .atom 0
def identity : Proof := .impIntro p (.hypothesis p)

#eval check (.imp p p) identity -- true
```

MiniLean uses these natural-deduction rules:

| Proof constructor | Meaning |
| --- | --- |
| `hypothesis p` | Use `p` when it is present in the context |
| `impIntro p body` | Assume `p` while proving `body`, yielding `p → body` |
| `impElim f x` | Apply a proof of an implication to a proof of its premise |
| `andIntro left right` | Build a conjunction from proofs of both sides |
| `andLeft pair`, `andRight pair` | Project either side of a conjunction |
| `orLeft q proof`, `orRight p proof` | Introduce one side of a disjunction |
| `orElim ...` | Prove a shared result by cases on a disjunction |
| `falseElim goal proof` | Derive any goal from falsehood |

## Project structure

```text
MiniLean/
  Core.lean       Formula, context, and proof-term syntax
  Checker.lean    Executable inference and theorem checking
  Examples.lean   Sample proofs and evaluated checks
Main.lean         Command-line entry point
lakefile.toml     Lake package and targets
lean-toolchain    Pinned Lean version
```

## Roadmap

The stages below are deliberately ordered so each one leaves MiniLean in a
usable state. A stage is complete when its listed behavior is implemented,
documented, and covered by examples or properties.

### Stage 0 — Project foundation (current)

**Purpose:** establish the Lean package and its first proof-checking loop.

**Work included:**

- Define formulas, contexts, and proof terms.
- Implement inference and goal checking.
- Include representative valid derivations.
- Document the package and pin its toolchain.

**Completion criteria:** `lake build` succeeds, the executable runs, and the
sample derivations are accepted.

**Status:** implemented; compilation still needs to be confirmed in a Lean
installed environment.

### Stage 1 — Logic completeness and checker behavior

**Purpose:** make the core rules precise and the checker easy to exercise.

**Work to accomplish:**

- Add negation and biconditional syntax with explicitly documented rules.
- Define a structured error type instead of returning only `none`, including
  errors for missing assumptions, wrong implication arguments, and invalid
  case branches.
- Add examples for every proof constructor, including rejected proof terms.
- Decide and document how duplicate assumptions and shadowing behave.
- Add context-management helpers and formula rendering suitable for errors.

**Completion criteria:** every core rule has positive and negative examples;
invalid proofs report which rule failed; the behavior of contexts is specified.

### Stage 2 — Formula and proof pretty-printing

**Purpose:** make MiniLean terms readable before introducing source files.

**Work to accomplish:**

- Print formulas with precedence-aware parentheses.
- Assign stable display names to atomic proposition IDs.
- Print proof trees in a compact, readable form.
- Add round-trip-oriented formatting conventions and examples.

**Completion criteria:** nested formulas render without ambiguity, and proof
trees can be inspected from the command line or in Lean examples.

### Stage 3 — Lexer and parser

**Purpose:** allow users to write MiniLean source instead of constructing Lean
datatypes by hand.

**Work to accomplish:**

- Specify a small textual grammar for formulas, contexts, and proof terms.
- Implement tokenization with source positions.
- Parse formulas and proof expressions with clear precedence rules.
- Report malformed tokens, missing delimiters, and unexpected input with line
  and column information.
- Add examples of valid and invalid source snippets.

**Completion criteria:** documented source files parse deterministically, and
syntax errors identify where parsing failed.

### Stage 4 — Source files and command-line checker

**Purpose:** make MiniLean useful as a standalone command-line tool.

**Work to accomplish:**

- Define a file format for declarations, assumptions, goals, and proofs.
- Extend the executable to accept file paths and check declarations.
- Print readable success or failure results, including source locations.
- Choose meaningful process exit codes for accepted and rejected files.
- Add help and usage output.

**Completion criteria:** users can run MiniLean on a file and get a clear
result without editing `Main.lean`.

### Stage 5 — Proof scripts and basic tactics

**Purpose:** reduce the amount of proof-term syntax users need to write.

**Work to accomplish:**

- Design a small tactic/script syntax.
- Implement `intro`, `exact`, `apply`, `assumption`, and conjunction tactics.
- Track and display the current goal and local context.
- Translate successful tactic scripts to proof terms, then pass those terms
  through the same checker.
- Explain failed tactic steps without weakening the checker.

**Completion criteria:** representative propositional theorems can be proved
with scripts, and generated terms are checked by the core.

### Stage 6 — Soundness connection

**Purpose:** establish a formal relationship between MiniLean proofs and Lean
propositions.

**Work to accomplish:**

- Define a translation from MiniLean formulas to Lean `Prop`.
- Define or relate proof-term typing to inhabitation of the translated
  proposition under translated assumptions.
- Prove that every proof accepted by MiniLean corresponds to a valid Lean
  derivation (soundness).
- Keep the executable checker and its specification aligned.

**Completion criteria:** the soundness theorem is proved in Lean, and the
trusted computing base and exact theorem statement are documented.

### Stage 7 — Quantifiers and variables

**Purpose:** move from propositional logic to first-order logic.

**Work to accomplish:**

- Add terms, variables, predicates, and universal and existential quantifiers.
- Specify variable binding and substitution carefully.
- Prevent variable capture during substitution.
- Extend parsing, printing, proof rules, and soundness results.
- Add examples such as quantified implication and witness construction.

**Completion criteria:** quantified examples parse, check, and have a proved
soundness connection.

### Stage 8 — Arithmetic and reusable libraries

**Purpose:** provide useful developments users can build on.

**Work to accomplish:**

- Define MiniLean's natural numbers and basic arithmetic propositions.
- Prove foundational results about equality, addition, and order.
- Add reusable libraries for lists, relations, and finite sets.
- Organize modules with documented import boundaries and naming conventions.
- Provide longer tutorial developments that demonstrate the system end to end.

**Completion criteria:** the library contains useful, independently checked
theorems and a tutorial proof using multiple modules.

### Stage 9 — Usability, editor support, and release

**Purpose:** make the project comfortable to learn, contribute to, and use.

**Work to accomplish:**

- Improve diagnostics, source spans, and formatting consistency.
- Add editor integration where practical, such as syntax highlighting and
  goal display.
- Document architecture, grammar, trusted core, and contributor workflow.
- Add automated build and example-checking automation for GitHub.
- Publish a versioned release with a changelog and stable examples.

**Completion criteria:** a new user can install MiniLean, follow the tutorial,
check a proof file, and understand where to report issues or contribute.

## Design principles

1. **One checker:** parsed proofs, tactic-generated proofs, and hand-built
   examples all go through the same checker.
2. **Small trusted core:** convenience features may search for proofs, but they
   cannot declare a theorem accepted without core checking.
3. **Explicit semantics:** syntax and rules are documented before features are
   added.
4. **Useful errors:** rejected inputs should help users find the problem.
5. **Prove important properties:** where practical, formalize correctness
   claims about the checker and transformations.

## Contributing

Start with a roadmap stage or a focused issue. Keep changes small enough to
review, include examples for new language behavior, and update the relevant
documentation when syntax or semantics change. Before submitting a change, run
`lake build` and include the result in your pull request description.

## License

No license has been selected yet. Until one is added, the repository does not
grant permission to reuse or redistribute its contents beyond rights provided
by applicable law. Choose and add a license before inviting external reuse.
