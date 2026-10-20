# Third-party source attribution and observed license scope

## TopCatModelCategory

The `lean/TopCatModelCategory/` sources in this companion reuse work from Joël Riou's [topcat-model-category](https://github.com/joelriou/topcat-model-category) at commit [`6c0c356fea469689fe76baeb47ba773460dfacee`](https://github.com/joelriou/topcat-model-category/tree/6c0c356fea469689fe76baeb47ba773460dfacee). They supply existing ordinary topological-space and simplicial-set model-category formalizations. Some files were adapted for this companion's Lean and Mathlib versions; they are reused upstream work, not newly independent proofs of those results. The companion's [EXISTING_FORMALIZATIONS.md](EXISTING_FORMALIZATIONS.md) records the mathematical reuse decisions and compatibility work.

The upstream copyright and author notices are retained in the five included files that carry them:

| File | Notice in the pinned upstream source |
| --- | --- |
| `lean/TopCatModelCategory/II.lean` | Copyright (c) 2025 Joël Riou; Author: Joël Riou; header states Apache 2.0. |
| `lean/TopCatModelCategory/Convenient/GeneratedBy.lean` | Copyright (c) 2025 Joël Riou; Author: Joël Riou; header states Apache 2.0. |
| `lean/TopCatModelCategory/PseudoFunctor/LaxNatTrans.lean` | Copyright (c) 2024 Joël Riou; Authors: Joël Riou and Yuma Mizuno; header states Apache 2.0. |
| `lean/TopCatModelCategory/SSet/Simplices.lean` | Copyright (c) 2025 Joël Riou; Author: Joël Riou; header states Apache 2.0. |
| `lean/TopCatModelCategory/SSet/Subcomplex.lean` | Copyright (c) 2024 Joël Riou; Author: Joël Riou; header states Apache 2.0. |

The adapted `SSet/Simplices.lean` and `SSet/Subcomplex.lean` files now also carry
explicit modification notices after their preserved upstream headers. The other
three files in this table are byte-identical to the pinned upstream sources.

**Unconfirmed repository-wide license scope:** The pinned upstream repository snapshot contains no repository-level `LICENSE` or `NOTICE` file, although those five headers refer to a `LICENSE` file. The remaining included upstream files do not carry that header. This record documents provenance and preserves the observed file-level notices; it does not assign a verified repository-wide license to the copied sources. The companion's own Apache-2.0 `LICENSE` describes its original project code and does not, by itself, establish the terms for upstream files. Confirm the applicable upstream terms or obtain an explicit statement from the upstream rights holders before publishing the copied sources, then update this section with the confirmed license text and any required notices.
