# Instructions for agents

This repository formalizes, in Lean 4, the plan that [README.md](README.md)
links to. It builds on Mathlib, and on the other libraries that
`lakefile.toml` requires, at the versions pinned in `lake-manifest.json`.
Read the plan's pages for the statements, the sources and the routes to a
proof, and follow the conventions on its front page, which keep the
milestones independent of each other.

## Building

```sh
lake exe cache get      # Mathlib's compiled files; takes a minute
lake build --wfail
```

`--wfail` makes every warning an error, as CI does, so a `sorry` fails the
build. Before you push, `lake build --wfail` must succeed.

## Layout

- The library is under `Ramsey/`, in the namespace `Ramsey`. Use one file
  per topic.
- No file imports the whole library. `lake build` builds every file under
  `Ramsey/` by itself (the `globs` in `lakefile.toml`), so a new file needs
  no import anywhere else. Do not add a file that imports the others.

## Lean's module system

Every file is a module, and starts like this:

```lean
module

public import Mathlib.Algebra.Group.Defs
public import Ramsey.Basic

/-!
# Title

What the file contains: its main definitions and results, and its sources.
-/

public section

namespace Ramsey

…

end Ramsey

end
```

- A module can import only modules, so every file starts with `module`.
- Import with `public import`, so that files that import yours see the
  declarations your statements use.
- Only declarations in a `public section`, or marked `public`, are visible to
  other files. A helper lemma that no other file needs can be `private`.
- Other files see a definition's type, but not its body, unless it is
  exposed. If other files need to unfold a definition, with `unfold`,
  `simp [foo]`, `rfl` or `decide`, write `@[expose] public section` instead,
  or put `@[expose]` on the definition. Theorems need no `@[expose]`.

## Rules

- **Use what exists.** Before you define or prove anything, search Mathlib
  (`.lake/packages/mathlib/Mathlib/`) and the other libraries in
  `.lake/packages/` for it, and use what you find. Where the plan says that a
  result exists in a library, do not reprove it.
- **State what the plan states.** A theorem that formalizes a milestone has
  the plan's hypotheses and conclusion, in the plan's generality. Weaker or
  different statements are not the milestone. Its docstring names the
  milestone, for example "This is the milestone *Torsion of E_n*".
- **No gaps.** No `sorry`, `admit`, new `axiom`, or `native_decide`.
- **Mathlib style.** Follow Mathlib's naming conventions and style. Every
  definition and every main theorem has a docstring, and every file starts
  with a module docstring that says what it contains.
- **Leave the setup alone.** Do not change `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` or anything under `.github/`,
  unless the issue you work on asks for it and a person in the project
  opened it.
- **Proofs check quickly.** A declaration that takes more than a few seconds
  to check slows every build that follows. Prefer an argument to a search:
  use symmetry to make finite checks small, and split `decide` into small
  cases rather than running it on a large one.
- **Keep pull requests focused.** One pull request does one issue. If an issue
  is too big for a pull request of a few hundred lines, split it into smaller
  issues instead.

## Reviewing

Besides building, check each main theorem of the pull request with
`#print axioms`, in a scratch file that you do not commit:

```lean
import Ramsey.Foo

#print axioms Ramsey.foo_bar
```

Run it with `lake env lean Scratch.lean`. A theorem may depend only on
`propext`, `Classical.choice` and `Quot.sound`.
