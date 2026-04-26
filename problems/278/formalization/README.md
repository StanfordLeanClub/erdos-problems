# Formalization status for Problem 278

This directory tracks the Lean formalization corresponding to the corrected v10/v12 paper draft and frontier note.

The current Lean development formalizes the stable **packing spine** of the project. It does **not** formalize the demoted weighted maximum claims from the older v9 draft, and it does **not** yet formalize the post-v10 full-union layer optimization results.

## Current snapshot

The present Lean snapshot includes:

1. the product-space cylinder model, cylinder disjointness, and perfect packing;
2. the pair-support theorem;
3. the common-core theorem with the explicit core/link disjointness hypothesis;
4. the graph-link abstraction layer and color-count predicates;
5. graph-link stars and their exact color criteria;
6. complete-bipartite graph-link setup and structural lemmas;
7. the exact complete-bipartite formula in the small-side regime `a < d`.

This matches the corrected paper claim about what is currently formalized.

## What the Lean currently supports

The Lean development supports the following stable claims:

- finite product-space cylinder definitions;
- cylinder disjointness as disagreement on common constrained coordinates;
- perfect packing as pairwise disjointness of chosen cylinders;
- the pair-support criterion;
- the common-core theorem, with the core/link disjointness assumption explicit;
- graph-link packaging of the color-count invariant;
- exact star criteria;
- complete-bipartite structural facts;
- exact complete-bipartite small-side theorem.

## What the Lean does not currently formalize

The current Lean project does **not** formalize:

- the old nonuniform clique criterion using `c_i - 2`;
- arbitrary-weight clique threshold formulas;
- any claim that packable-subgraph optimization is the same as full #278 maximum coverage;
- the layer-union objective `U_d(H)`;
- the full-capacity one-layer matching-polynomial theorem;
- the clique-layer defect-cover lemma;
- the exact full-union theorem for `K_n,t=n-3`;
- the residual-core certificate for `K_n,t=n-4`;
- the star–triangle normal form for arbitrary graph links.

Those are either corrected/demoted in v10, stabilized but not formalized in v12, or still future work.

## v12 note

The v12 full-union residual-core results are not currently Lean-formalized. The Lean code still covers the packing spine. The residual-core certificate for \(K_n,t=n-4\) is an external certificate/checker target, not a Lean theorem.

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

At the present stage, the Lean development supports the corrected paper's claim that the formalization reaches:

- the finite core theory;
- the graph-link abstraction layer;
- stars;
- a substantial complete-bipartite packability package, including the exact small-side complete-bipartite theorem.

The Lean development should be described as formalizing **packing** and **packability-side graph-link theory**, not the full #278 maximum-coverage objective.

## Build metadata

This scaffold includes the working package metadata from the local project:

- `lean-toolchain` — `leanprover/lean4:v4.29.0`
- `lakefile.toml` — package name `erdos278`, default target `Erdos278`
- `lake-manifest.json` — locked dependency snapshot

The manifest records `mathlib` at `v4.29.0` and additional packages inherited from the local environment such as `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli`.

The essential package declaration in `lakefile.toml` is the `mathlib` dependency and the `Erdos278` Lean library; the manifest preserves the exact environment used in the uploaded local project.

## Build / reproduce

From `problems/278/formalization/lean/`:

```bash
lake update
lake build
```

If you want to reproduce the local project as closely as possible, keep the committed `lake-manifest.json`.

If you want a lighter repository, you can omit the manifest and let `lake update` regenerate it from `lakefile.toml`, at the cost of potentially picking up slightly different transitive dependency revisions later.

## Best next formalization targets

1. Finish the remaining complete-bipartite packability regime `a >= d`.
2. Formalize the star–triangle normal form for `chi_d(F)` as a packable-color invariant.
3. Formalize/check the one-layer `K4` example separating packable-subgraph value from full union value.
4. Formalize corrected clique-link criteria only after the corrected proof is fully stabilized.
5. Define the layer-union objective `U_d(H)` once the mathematical formulation is stable enough.
6. Eventually formalize the full-capacity one-layer matching-polynomial theorem and the `K_n,t=n-3` theorem.
7. Treat the `K_n,t=n-4` residual-core certificate as external until it is converted into a Lean-friendly proof object.
