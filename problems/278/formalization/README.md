# Formalization status for Problem 278

This directory tracks the Lean formalization corresponding to the current paper draft and frontier note.

## Current snapshot

The uploaded source tree formalizes material that goes materially beyond the original finite core. In particular, the present snapshot includes:

1. the product-space cylinder model, cylinder disjointness, and perfect packing
2. the pair-support theorem
3. the common-core theorem with the explicit core/link disjointness hypothesis
4. the graph-link abstraction layer and color-count predicates
5. graph-link stars and their exact color criteria
6. complete bipartite graph-link setup and structural lemmas
7. the exact complete-bipartite formula in the small-side regime `a < d`

## Module map

### Core
- `Erdos278/BasicDefs.lean` — basic product-space objects, supports, cylinders, perfect-packability predicate
- `Erdos278/PerfectPacking.lean` — cylinder disjointness criterion and pairwise-disjoint reformulation
- `Erdos278/PairSupports.lean` — pair-support theorem
- `Erdos278/CommonCore.lean` — common-core theorem and its supporting equivalences
- `Erdos278/Erdos278Core.lean` — grouped imports for the finite core

### Star family layer
- `Erdos278/Stars.lean` — star-family definitions and exact perfect-packability / color criteria
- `Erdos278/StarColoring.lean` — coloring constructions and auxiliary lemmas for star-packability arguments

### Graph-link abstraction layer
- `Erdos278/GraphLinks/Basic.lean` — graph-link definitions and basic predicates
- `Erdos278/GraphLinks/Stars.lean` — graph-link stars
- `Erdos278/GraphLinks/Chi.lean` — abstract color-count predicate `ChiPackLinkLe` and least-color invariant `chiPackLink`
- `Erdos278/GraphLinks/ChiStars.lean` — minimal-color invariant for stars

### Complete bipartite graph-link layer
- `Erdos278/GraphLinks/BipartiteBasic.lean` — complete bipartite link definitions and elementary structure
- `Erdos278/GraphLinks/BipartiteIntersecting.lean` — intersecting-family structure inside complete bipartite links
- `Erdos278/GraphLinks/BipartiteStars.lean` — singleton-side reductions to stars and star-based consequences
- `Erdos278/GraphLinks/BipartitePack.lean` — packability-side consequences for complete bipartite links
- `Erdos278/GraphLinks/BipartiteUpperHelpers.lean` — helper constructions for upper-bound and coloring arguments
- `Erdos278/GraphLinks/BipartiteExactSmallSide.lean` — exact small-side theorem for complete bipartite links

### Top-level import file
- `Erdos278.lean` — aggregate imports for the current formalized library

## Current prose summary

At the present stage, the Lean development supports the paper's claim that the formalization reaches:
- the finite core theory
- the graph-link abstraction layer
- stars
- a substantial complete-bipartite packability package, including the exact small-side complete-bipartite theorem

## Build metadata now included

This scaffold now includes the working package metadata from the local project:

- `lean-toolchain` — `leanprover/lean4:v4.29.0`
- `lakefile.toml` — package name `erdos278`, default target `Erdos278`
- `lake-manifest.json` — locked dependency snapshot

The manifest currently records, among others, `mathlib` at `v4.29.0` and additional packages inherited from the local environment such as `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`. The essential package declaration in `lakefile.toml` is the `mathlib` dependency and the `Erdos278` Lean library; the manifest preserves the exact environment used in the uploaded local project.

## Build / reproduce

From `problems/278/formalization/lean/`:

```bash
lake update
lake build
```

If you want to reproduce the local project as closely as possible, keep the committed `lake-manifest.json`. If you want a lighter repository, you can omit the manifest and let `lake update` regenerate it from `lakefile.toml`, at the cost of potentially picking up slightly different transitive dependency revisions later.

## Best next formalization targets

1. the remaining complete-bipartite regime `a >= d`
2. clique-link packability theorems
3. weighted clique theorems
4. triangle-free and one-full-side weighted theorems
5. later, the star–triangle and separator/interface exact-solvability machinery
