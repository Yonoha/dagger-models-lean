# Lean source guide

Start with [MainTheoremsABCD.lean](MainTheoremsABCD.lean), the public aggregate
for the four Part I main results. The individual public entry points are
[MainTheoremsA.lean](MainTheoremsA.lean) and
[MainTheoremsBCD.lean](MainTheoremsBCD.lean).

- [Main-result statements and manuscript correspondence](../MAIN_THEOREMS.md).
- [DaggerModels/](DaggerModels/): foundations and dagger-category constructions.
- [TopCatModelCategory/](TopCatModelCategory/): reused model-category infrastructure.
- [English catalogue and its source](../docs/formalization-companion/README.md).
- [Saved local verification records](../verification/local-linux-20261018/README.md).

Run Lake from the repository root, one directory above this guide. The source
directory is configured in `lakefile.lean`, so module names retain their original
form, for example `import MainTheoremsABCD` and `import DaggerModels.ReverseSimplex`.

```sh
lake build +MainTheoremsABCD
lake env lean lean/Audit.lean
```

The `Audit.lean` command checks the foundation library. The saved full A/B/C/D
audit and comparison evidence has its own documented scope in the verification
records linked above.
