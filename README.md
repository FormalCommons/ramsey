# Lean project template

A starting point for a Lean 4 formalization that AI agents build through
[fc-worker](https://github.com/FormalCommons/fc-worker): agents work on the
repository's issues, open pull requests and review them, and GitHub's merge
queue merges the approved ones. It holds what the first experiment,
[congruent-numbers](https://github.com/FormalCommons/congruent-numbers),
showed a project needs from the start:

- **No root import file.** `lakefile.toml` builds every module under
  `Project/` through `globs`. When every pull request adds a line to one
  import file, each merge puts the other open pull requests in conflict.
- **Lean's module system**, explained in [AGENTS.md](AGENTS.md), so that
  every file is a module from the start.
- **CI that restores built dependencies.** The `cache` workflow builds Mathlib
  and the other dependencies on main and saves them; CI on pull requests and
  in the merge queue restores them instead of downloading and building them
  again. CI does not run again on main after a merge, since the merge queue
  has already built exactly that commit.
- **A review check** for axioms, in AGENTS.md.

## Starting a project

1. Create the repository from this template:
   `gh repo create FormalCommons/<name> --public --template FormalCommons/lean-project-template`.
2. Rename `Project` to the library's name in `lakefile.toml`,
   `lake-manifest.json` (`"name"`), `AGENTS.md`, the folder `Project/` and
   the namespace. Add the libraries the plan builds on to `lakefile.toml`,
   and update the versions with `lake update`. Replace `Project/Basic.lean`.
3. Replace this README with one for the project, which links to the plan
   that AGENTS.md refers to.
4. Set the repository up as fc-worker's README says: the Apps' access, the
   labels, the ruleset with the merge queue, auto-merge, and a read-only
   `GITHUB_TOKEN` for Actions.
5. Run the cache workflow once: `gh workflow run cache`. It runs again by
   itself whenever `lake-manifest.json` or `lean-toolchain` changes on main.

## Building

```sh
lake exe cache get
lake build --wfail
```
