# Monotone circuit bounds for crowns

The model is `PEqualNP.Represents.RepSizeAtMost`. The circuit uses fan-in-two AND/OR gates and has to agree with the bipartite adjacency matrix only when exactly one left input and one right input are on. For the crown of size `n` on each side, the adjacency test is `u ≠ v`.

| Side length | Minimum number of gates | Lean theorem |
| --- | --- | --- |
| 7 | 23 | [`CrownLower.crownSevenMinimum`](CrownLower.lean#L252) |
| 8 | 27 | [`CrownExact.crownSize27`](CrownExact.lean#L162) |
| 9 | 30 | [`CrownProduct.crownNineExact`](CrownProduct.lean#L61) |
| 10 | 34 | [`CrownTenExact.crownTenExact`](CrownTenExact.lean#L18) |

Lean also checks the lower bound `3*n + 4` for every `n ≥ 10` and a circuit of size 55 for `n = 16`. [General bound](CrownTenExact.lean#L54) · [55-gate circuit](CrownGridBounds.lean#L127)

The combined mathematical and computational arguments give exact sizes 38, 41, 45 and 55 at side lengths 11, 12, 13 and 16. The lower bounds use finite computations in Python and Z3 in addition to the Lean reductions. At `n = 16`, the lower bound excludes 38 gates for threshold two on 16 inputs, which excludes 54 gates for the crown and implies the bound `3*n + 7` for every `n ≥ 16`. The finite exclusion appears as a hypothesis in the Lean lower-bound theorem. [Conditional lower bound](CrownSixteenFrontier.lean#L58) · [Proof for size 16](crown-sixteen.md) · [Project discussion](https://github.com/open-goat/pequalnp-proofs/discussions/38248)

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

## Finite profile checks for sizes 11, 13 and 16

Run these commands from `research/crown-bounds` with Python 3 and Z3 4.16.0 on `PATH`. The commands use a separate directory for generated systems and results. Each run keeps satisfiable or unresolved cases in JSON for inspection and refinement.

```sh
export CROWN_RUNS="$PWD/profile-runs"
python3 crown11_or_profiles.py
python3 crown11_and_profiles.py
python3 crown13_profiles.py or
python3 crown13_matching_output.py
python3 crown13_profiles.py and
python3 crown13_profiles.py refine
```

The arguments for the finite checks and the mathematical elimination of their listed residual layouts are in the notes for [size 11](crown-eleven.md) and [size 13](crown-thirteen.md). In the size-13 output check, 54 of the 30,240 formulas meet the first conditions, and none passes all the tests.

For size 16, the graph generators enumerate all possible counts of shared signals and all positions of the first shared formula with an AND. The refinement steps check values on pairs and divide remaining cases by the singleton profiles witnessing the first AND.

```sh
python3 crown16_profiles.py or
for stages in 4 5 6 7; do
  python3 crown16_profiles.py and "$stages" || exit
  for first in $(seq 3 "$stages"); do
    python3 crown16_profiles.py refine "$first" "$stages" --timeout 2500 || exit
    python3 crown16_profiles.py refine "$first" "$stages" --pending --pair-models --timeout 10000 || exit
  done
done
python3 crown16_profiles.py refine 3 7 --pending --triples --timeout 10000
python3 crown16_profiles.py split 4 7 --timeout 1500
python3 crown16_profiles.py split 4 7 --exclusive --timeout 1500
python3 crown16_profiles.py split 4 7 --both-sides --timeout 1500
python3 crown16_profiles.py split 4 7 --both-sides --pending --pair-models --timeout 10000
```

These commands use the current constraints from the first pass. Counts left by each pass can vary with the solver and time limits. To reproduce the exclusion, the final split output `crown16_split_7_4_both.json` and each `crown16_refined_<stages>_<first>.json` outside the `(7,4)` split must be empty lists. Increase the timeout on any unresolved cases using the corresponding `--pending` command. The notes record the original run, including the final 22 split branches and their `unsat` results. [Size-16 proof and run counts](crown-sixteen.md)

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

## Partial pairings at size 19

Every projection onto one block of a minimal size-19 circuit must retain exactly 11 gates with distinct tables. The four-merger case with three of one orientation, one of the other orientation and zero diagonal overlap is unsatisfiable under these constraints in CaDiCaL. With three cross-block ORs, the first attachment of an unmerged port has only two possible argument tables on the three merged signals. One of the two tables remains possible when opposite orientations share a diagonal label. [Proof of the restrictions](crown-blocks.md#первый-общий-сигнал-при-трёх-объединениях)

Lean also checks an optimal 11-gate circuit in which all eight ports are used once and one diagonal pair has no direct connecting gate. Its two ports meet along an unshared OR chain. [Construction and correctness](CrownBlocks.lean#L172)

```sh
mkdir -p partial-runs
solver=$(command -v cadical)
python3 crown_partial_sat.py 19 4 partial-runs --solver "$solver" --seconds 45
python3 crown_four_patterns.py partial-runs/crown4.cnf --solver "$solver"
python3 crown_four_patterns.py partial-runs/crown4-or-region.cnf --solver "$solver" --or-region --seconds 48
```
