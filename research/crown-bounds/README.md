# Monotone circuit bounds for crowns

The model is `PEqualNP.Represents.RepSizeAtMost`. The circuit uses fan-in-two AND/OR gates and has to agree with the bipartite adjacency matrix only when exactly one left input and one right input are on. For the crown of size `n` on each side, the adjacency test is `u ≠ v`.

| Side length | Minimum number of gates | Lean theorem |
| --- | --- | --- |
| 7 | 23 | [`CrownLower.crownSevenMinimum`](CrownLower.lean#L252) |
| 8 | 27 | [`CrownExact.crownSize27`](CrownExact.lean#L162) |
| 9 | 30 | [`CrownProduct.crownNineExact`](CrownProduct.lean#L61) |
| 10 | 34 | [`CrownTenExact.crownTenExact`](CrownTenExact.lean#L18) |

Lean also checks the lower bound `3*n + 4` for every `n ≥ 10` and a circuit of size 55 for `n = 16`. [General bound](CrownTenExact.lean#L54) · [55-gate circuit](CrownGridBounds.lean#L127)

The exclusion of 54 gates at `n = 16` relies on finite computations in Python and Z3. This branch contains the Lean-checked reduction and normalization lemmas for that result. The finite exclusion appears as a hypothesis in the Lean statement, and the computational argument was reported separately. [Conditional lower bound](CrownSixteenFrontier.lean#L58) · [Project discussion](https://github.com/open-goat/pequalnp-proofs/discussions/38248)

## Reproduction

Use the toolchain pinned by `lean/lean-toolchain`. From the repository root, run the following commands. `modules.txt` orders the research modules by dependency. The final command prints the axioms used by the named theorems.

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs PEqualNP.Defs.Represents \
  PEqualNP.MetaComplexity.Helpers.LowMergeWires PEqualNP.Outside.L_meta_18677
bounds=../research/crown-bounds
while IFS= read -r mod; do
  lake env lean -R "$bounds" -o ".lake/build/lib/lean/$mod.olean" "$bounds/$mod.lean" || exit
done < "$bounds/modules.txt"
lake env lean -R "$bounds" "$bounds/Audit.lean"
```
