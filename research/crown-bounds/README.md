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
  PEqualNP.MetaComplexity.Helpers.LowMergeWires \
  PEqualNP.MetaComplexity.Helpers.TableSearch PEqualNP.Outside.L_meta_18677
bounds=../research/crown-bounds
while IFS= read -r mod; do
  lake env lean -R "$bounds" -o ".lake/build/lib/lean/$mod.olean" "$bounds/$mod.lean" || exit
done < "$bounds/modules.txt"
lake env lean -R "$bounds" "$bounds/Audit.lean"
```

## Disjoint four-by-four crowns

Lean checks circuits with 21 gates for two disjoint crowns and 43 gates for four. Pair a row input from one crown with a column input of the same label from the other. Eight ORs reduce a pair of crowns to one crown edge test on eight signals, with all singleton and same-side pair tests required to be negative. The residual circuit uses 13 gates and shares two pair ORs. [21/43-gate constructions](CrownBlocks.lean#L157) · [Promise equivalence](CrownQuotient.lean#L22)

When every original input is read exactly once by one of the eight cross-block ORs, 21 gates are necessary. The lower bound for the residual circuit combines CaDiCaL, exact formula enumeration, and a case analysis for four repeated inputs on a single side. The general budgets of 20 and 42 in the Desk remain open. [Argument in Russian](crown-quotient.md) · [SAT encoding](crown_quotient_sat.py) · [Formula enumeration](crown_quotient_formulas.py)

The general lower bounds for two and four crowns are 19 and 35. The 20-gate search reached its time limit. Lean also checks a general normalization lemma that moves an OR input that vanishes on all negative samples to the final output without increasing the circuit size. [Counting argument](crown-blocks.md) · [Normalization](CrownSafeOr.lean#L129)

To reproduce the finite search from this directory, use Python and CaDiCaL 2.1.2. The four `UNKNOWN` cases at size 12 are handled by the formula enumeration and the single-side argument above.

```sh
mkdir -p quotient-runs
for gates in 10 11 12; do
  python3 crown_quotient_sat.py "$gates" quotient-runs --solver "$(command -v cadical)" --seconds 20
done
python3 crown_quotient_formulas.py --seconds 35
```

## Partial cross-block pairings

With six or more cross-block ORs whose original arguments are used just once, choose which of the unmerged ports to keep so every quotient pair can still be tested. Removing the other ports reduces any size-20 circuit in this class to the strict eight-wire quotient with at most 12 gates, which is impossible. Lean checks coverage of the pair tests and the deduction of singleton tests. [Coverage lemma](CrownQuotient.lean#L52) · [Proof](crown-quotient.md#шесть-и-семь-объединений)

With five such ORs, one negative same-side pair can be left unchecked. A circuit missing only that test still needs at least 12 gates. This excludes five such ORs at size 19, and at size 20 if any original input is read repeatedly. The complete size-20 question remains open. [One-missing-test proof](crown-quotient.md#пять-объединений-и-один-пропущенный-тест)

The following commands reproduce the finite part of the 12-gate lower bound, by testing the strict quotient with one extra same-side edge. The strict quotient itself has the previously established 13-gate lower bound.

```sh
python3 crown_quotient_formulas.py --extra-edge --repeats 3
python3 crown_quotient_formulas.py --extra-edge --repeats 4
python3 crown_quotient_sat.py 11 quotient-runs --extra-edge --only-count 3 --solver "$(command -v cadical)"
```
