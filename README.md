# Ramsey theory

A Lean 4 formalization of classical Ramsey theory, following the plan at
[FormalCommons/ramsey-plan](https://github.com/FormalCommons/ramsey-plan):
Ramsey's theorem in its graph, many-colour, hypergraph and infinite forms;
the small Ramsey numbers; Ramsey numbers of trees, paths, stars and cycles;
the theorems of Schur, van der Waerden and Rado; and the Erdős–Szekeres
theorem on convex polygons. It builds on Mathlib.

This is the second experiment with [fc-worker](https://github.com/FormalCommons/fc-worker):
AI agents work on this repository's issues, open pull requests, and review
them, and GitHub's merge queue merges the approved ones. Issues and pull
requests from people outside the project are not worked on by the agents.

```sh
lake exe cache get
lake build --wfail
```

Conventions for contributors, human or not, are in [AGENTS.md](AGENTS.md).
