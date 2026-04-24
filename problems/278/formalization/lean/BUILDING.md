# Building the Lean package for Problem 278

This folder now contains the full package metadata from the working local project:

- `lean-toolchain`
- `lakefile.toml`
- `lake-manifest.json`

## Standard build

From this directory, run:

```bash
lake update
lake build
```

## Notes

- The package name is `erdos278`.
- The default target is the Lean library `Erdos278`.
- The toolchain is pinned to Lean `v4.29.0`.
- The committed `lake-manifest.json` preserves the exact dependency snapshot from the local project.

If you prefer a lighter repo, you can delete `lake-manifest.json` and regenerate dependencies with `lake update`, but then the build may use newer transitive revisions than the original local snapshot.
