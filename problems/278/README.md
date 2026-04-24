# Problem 278 — Maximum density of congruence covers

## Public problem
Erdős Problem #278 asks:

> Let \(A=\{n_1<\cdots<n_r\}\) be a finite set of positive integers. What is the maximum density of integers covered by a suitable choice of congruences \(a_i \pmod{n_i}\)?

The minimum-density side is publicly known to be settled; the live side is the **maximum** covered density.

## Current project status

- **Status:** paper-worthy partial progress; not a full solution
- **Current center of gravity:** squarefree common-core graph links
- **Operational perspective:** exact packability and weighted optimization in structured squarefree families
- **Current mathematical frontier:** exact weighted solvability via star–triangle structure and separator/interface dynamic programming on broad sparse graph-link classes
- **Current formalization frontier:** the finite core theory, graph-link layer, stars, and a substantial complete-bipartite packability package, including the exact small-side complete-bipartite theorem

## Folder guide

- `paper/current/` — canonical current paper draft
- `paper/archive/` — historically meaningful earlier snapshots
- `frontier/current/` — canonical current frontier note and visualizer YAML
- `frontier/README.md` — explains what the frontier note and frontier YAML are, which one is authoritative, and how to update them together
- `frontier/archive/` — older checkpoints
- `formalization/` — Lean source tree plus a theorem-to-file map
- `references/` — public links and lightweight reference material

## What this project currently claims

This project does **not** currently claim a full solution to #278.

What it does claim is a coherent finite structural theory for broad squarefree/common-core families, including:

- exact perfect-packability results through the common-core graph-link invariant
- exact packability theorems for stars, complete bipartite links, and clique-link regimes already isolated in the paper
- exact weighted results on several structured families
- a new exact-solvability program based on star–triangle decomposition and separator/interface dynamic programming
- a growing Lean formalization of the finite combinatorial core and part of the graph-link packability library

## Best entry points

1. `frontier/current/frontier_note.md`
2. `frontier/README.md`
3. `paper/current/erdos278_paper.pdf`
4. `formalization/README.md`
5. `status.yaml`

## Update convention for this folder

Treat the files in `current/` as canonical and stable.
When a new milestone is reached:
- replace the current artifact
- archive the older one only if it is worth preserving
- update `status.yaml`
- update this README if the high-level description changes
