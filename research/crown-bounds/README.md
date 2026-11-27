# Monotone circuit bounds for crowns, cycles, and incidence graphs

The model is `PEqualNP.Represents.RepSizeAtMost`. The circuit uses fan-in-two AND/OR gates and has to agree with the bipartite adjacency matrix only when exactly one left input and one right input are on. For the crown of size `n` on each side, the adjacency test is `u ≠ v`.

| Side length | Minimum number of gates | Lean theorem |
| --- | --- | --- |
| 7 | 23 | [`CrownLower.crownSevenMinimum`](CrownLower.lean#L252) |
| 8 | 27 | [`CrownExact.crownSize27`](CrownExact.lean#L162) |
| 9 | 30 | [`CrownProduct.crownNineExact`](CrownProduct.lean#L61) |
| 10 | 34 | [`CrownTenExact.crownTenExact`](CrownTenExact.lean#L18) |

Lean also checks the lower bound `3*n + 4` for every `n ≥ 10` and a circuit of size 55 for `n = 16`. [General bound](CrownTenExact.lean#L54) · [55-gate circuit](CrownGridBounds.lean#L127)

The combined mathematical and computational arguments give exact sizes 38, 41, 45 and 55 at side lengths 11, 12, 13 and 16. The lower bounds use finite computations in Python and Z3 in addition to the Lean reductions. At `n = 16`, the lower bound excludes 38 gates for threshold two on 16 inputs, which excludes 54 gates for the crown and implies the bound `3*n + 7` for every `n ≥ 16`. The finite exclusion appears as a hypothesis in the Lean lower-bound theorem. [Conditional lower bound](CrownSixteenFrontier.lean#L58) · [Proof for size 16](crown-sixteen.md) · [Project discussion](https://github.com/open-goat/pequalnp-proofs/discussions/38248)

Removing one positive cell from a five-by-five crown leaves a graph of exact minimum size 15. The transposed OR graph excludes 14 gates without a depth restriction. Lean checks the neighborhood inclusions and a 15-gate circuit in the original input order of mask `32435687`. [Combinatorial proof](crown-missing-cell.md) · [Lean witness](CrownMissingCell.lean#L46) · [Desk row L-meta-25467](https://pequalnp.com/desk/row?gap=L-meta-25467)

## Incidence graph after deleting one line

For a graph without a four-cycle, the stars obtained from the two raw OR-only operand sets of certain AND gates give a circuit lower bound. It counts the edges and a vertex cover of the union of these stars, plus the erased raw operand positions. For L-meta-9737, at least six of the 48 edges must lie outside these stars in any minimum circuit of size at most 58. The five-edge exclusion reduces to twelve line centers and one point center, then excludes both ways of using the spare union. Lean checks the 59-gate construction and the graph facts used in these arguments. [General bound](first-star-cover.md) · [Four-edge exclusion](first-star-four-exclusion.md) · [Five-edge restrictions](first-star-five.md) · [Spare-union analysis](first-star-five-spare.md) · [Five-edge exclusion](first-star-five-exclusion.md) · [Geometry checker](first_star_five_geometry.py) · [Lean certificate](PlaneRobustCover.lean) · [Desk row](https://pequalnp.com/desk/row?gap=L-meta-9737)

## Reproduction

Use the toolchain pinned by `lean/lean-toolchain`. From the repository root, run the following commands. `modules.txt` orders the research modules by dependency. The final command prints the axioms used by the named theorems.

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs PEqualNP.Defs.Represents \
  PEqualNP.MetaComplexity.Helpers.LowMergeWires \
  PEqualNP.MetaComplexity.Helpers.TableSearch PEqualNP.MetaComplexity.L154 \
  PEqualNP.Outside.L_meta_18677
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

**For every `k ≥ 1`, the exact minimum for `k` disjoint four-by-four crowns is `11k - 1` for even `k` and `11k` for odd `k`.** The lower bound permits arbitrary AND depth and sharing. In the transposed OR network, count how many positions each helper can introduce and how fully shared blocks can make up for a missing position. Equality forces disjoint helper pairs and rules out a fixed three-by-three crown under the exchange of sides. [Complete combinatorial proof](crown-all.md) · [87-gate witness for eight crowns in Lean](CrownBlocks.lean#L219)

For a union of `p` isolated edges, `a` three-by-three crowns, and `b` four-by-four crowns, the exact size is `2p + ceil(15a/2) + 11b - 1 + (b mod 2)`. A single edge by itself takes zero gates. The parity term persists when both crown counts are odd. [Proof for mixed unions](crown-mixed.md) · [Lean witnesses](CrownMixed.lean#L60)

For a union of bipartite cycles of lengths at least six with `N` vertices per side, the bound `2N - 1 + ceil(N/2)` is tight exactly when all lengths have even multiplicity, or there is one odd multiplicity at a length congruent to two modulo four. For `k` copies of a common cycle of length `2n`, the bound is exact except when `n` is even and `k` is odd, when the exact minimum is `5nk/2 + 1`. The upper construction uses at most one AND per path. [Cycle proofs](cycle-promise.md) · [Lean generator for even half-length](CyclePromise.lean#L61)

For regular bipartite components of a common degree at least two with distinct same-side neighborhoods, let `u` count component types of odd multiplicity, allowing transpose within a type. The lower bound is `2N - 1 + ceil((N+u)/2)`. For cycles this is exact when the types of even half-length all have even multiplicity. With even `N`, any odd-multiplicity type of even half-length forces at least two gates above the basic bound. [Proof for mixtures and regular components](cycle-mixtures.md) · [61-gate mixed witness in Lean](CyclePromise.lean#L163)

Pair a row input from one crown with a column input of the same label from the other. Eight ORs reduce a pair of crowns to one crown edge test on eight signals, with all singleton and same-side pair tests required to be negative. The residual circuit uses 13 gates and shares two pair ORs. [21/43-gate constructions in Lean](CrownBlocks.lean#L161) · [Promise equivalence](CrownQuotient.lean#L22)

When every original input is read exactly once by one of the eight cross-block ORs, 21 gates are necessary. The lower bound for the residual circuit combines CaDiCaL, exact formula enumeration, and a case analysis for four repeated inputs on a single side. [Argument in Russian](crown-quotient.md) · [SAT encoding](crown_quotient_sat.py) · [Formula enumeration](crown_quotient_formulas.py)

The same formula had been proved by separate arguments for small numbers of blocks. [Two and four crowns](crown-demand.md) · [Three crowns](crown-three.md) · [Five crowns](crown-five-exact.md) · [Six crowns](crown-six.md) · [Seven crowns](crown-seven.md) · [Lean witnesses](CrownBlocks.lean#L161)

The separate projection argument shows that two blocks can always be chosen so that zeroing them saves at least 17 gates. [Projection argument](crown-four.md#зануление-двух-выбранных-блоков)

For circuits with at most one AND on each input-output path, the exact minimum is `11k - 1` for even `k` and `11k` for odd `k`. This allows arbitrary sharing and arbitrarily many products. Transposing the OR layer reduces the lower bound to two families of sets per block. Lean checks the six-gate lower bound for one of the support configurations and the 11-gate single-block witness. [Layered proof](crown-four.md#схемы-с-одним-and-на-каждом-пути) · [Support lemma](CrownLayered.lean#L30) · [Single-block witness](CrownBlocks.lean#L181)

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

## Exclusion of size 19

Every projection onto one block of a minimal size-19 circuit must retain exactly 11 gates with distinct tables. The argument maximizes direct cross-block ORs by reassociating unshared OR chains and leaves seven cases. CaDiCaL excludes six directly. The last case reduces to an 11-gate one-crown property. When both ports of a diagonal pair are read once and enter ORs, their paths must meet using only ORs before either path branches. The proof lifts the unshared paths from the projection to the input circuit. [Full case analysis](crown-blocks.md#исключение-бюджета-19)

Lean checks the exact size 10 of both restrictions obtained by setting three combined signals to zero. Lean also checks an optimal 11-gate circuit in which all eight ports are used once and one diagonal pair meets through two OR gates in series. [Lean declarations](CrownBlocks.lean)

```sh
mkdir -p partial-runs
solver=$(command -v cadical)
python3 crown_partial_sat.py 19 3 partial-runs --solver "$solver" --shape 2 1 0 --seconds 60
python3 crown_partial_sat.py 19 3 partial-runs --solver "$solver" --shape 2 1 1 --expose-pairs --seconds 100
python3 crown_partial_sat.py 19 4 partial-runs --solver "$solver" --shape 2 2 0 --shape 3 1 0 --seconds 45
python3 crown_partial_sat.py 19 4 partial-runs --solver "$solver" --shape 2 2 1 --shape 3 1 1 --expose-pairs --seconds 85
python3 crown_four_patterns.py partial-runs/crown4-once-first-or.cnf --solver "$solver" \
  --ports pair-once --or-region --pair-first-or --seconds 90
```

Each selected case and the one-crown test must return `UNSAT`. The single-crown exclusion uses SHA-256 `380654d65bf4085f5b6ba4d97a4b5250c0354b41e4db949b92a8ae9f11350293` for its generated CNF and also passed a run with CaDiCaL's internal DRAT and LRAT checking enabled. The five-or-more-pair cases use the earlier quotient checks described above.

## Reduction of the size-20 cases

Use a representative that minimizes the number of gates active on a negative test, then maximizes direct cross-block ORs whose two original inputs are read once. Every configuration with pairs of both orientations is excluded, as is the four-pair case with all pairs in one orientation. A size-20 circuit consequently has at most three pairs in one orientation and must save nine gates on deleting at least one block. [Proof and case counts](crown-quotient.md#зануление-целого-блока-при-объединениях-в-обоих-направлениях) · [Single orientation](crown-quotient.md#четыре-объединения-одного-направления)

The partially specified eight-wire problems below all need at least 12 gates. The formula checks cover size 10 and the four repeated-input case at size 11. The SAT check covers the remaining size-11 case with three repeated inputs. The omitted pairs are free in each test.

```sh
for shape in overlap-0 overlap-1 overlap-2 triangle disjoint \
  triangle-overlap-1 triangle-overlap-2 triangles-overlap-2 triangles-overlap-3; do
  python3 crown_quotient_formulas.py --unchecked "$shape" --repeats 3 || exit
  python3 crown_quotient_formulas.py --unchecked "$shape" --repeats 4 || exit
  python3 crown_quotient_sat.py 11 partial-runs --solver "$solver" \
    --unchecked "$shape" --only-count 3 || exit
done
```

Each case in this loop must return `UNSAT`. For the four-pair case `(2,2,0)`, the additional projection check below must exclude every pattern with two or three repeated inputs. The pattern with four repeated inputs is retained for the full-circuit test. Both projections then force all four combined signals to be reused in the original circuit.

```sh
python3 crown_quotient_sat.py 12 partial-runs --solver "$solver" --unchecked overlap-0 \
  --sole-or 0 1 6 7 --only-count 2 --seconds 40
python3 crown_quotient_sat.py 12 partial-runs --solver "$solver" --unchecked overlap-0 \
  --sole-or 0 1 6 7 --only-count 3 --seconds 40
python3 crown_partial_sat.py 20 3 partial-runs --solver "$solver" --expose-pairs --seconds 75
python3 crown_partial_sat.py 20 4 partial-runs --solver "$solver" --expose-pairs \
  --shape 2 2 0 --seconds 110
python3 crown_partial_sat.py 20 4 partial-runs --solver "$solver" --expose-pairs \
  --shape 2 2 1 --shape 2 2 2 --shape 3 1 0 --shape 3 1 1 --seconds 75
```

The full-size tests above return `UNSAT`. The Lean coverage lemma transfers visible pair tests and the singleton tests implied by negative pairs to a restricted quotient. [Lean coverage lemma](CrownQuotient.lean#L88)

For `(3,2,2)`, both projection checks below return `UNSAT` on all their branches. Each projection must therefore reuse at least four combined signals. The full-size check uses this constraint and returns `UNSAT`.

```sh
for count in 2 3; do
  python3 crown_quotient_sat.py 12 partial-runs --solver "$solver" --unchecked single-shifted \
    --sole-or 3 6 7 --only-count "$count" --seconds 28 || exit
done
python3 crown_partial_sat.py 20 5 partial-runs --solver "$solver" --expose-pairs \
  --shape 3 2 2 --seconds 110
```

For `(3,2,1)`, the projection check excludes every two-repeat pattern. For three repeats, the only pattern the check needs to retain has `L0`, `R3`, and one of `L1` or `L2` repeated. This constraint and the four- and five-repeat patterns together give `UNSAT` in the full circuit.

```sh
for count in 2 3; do
  python3 crown_quotient_sat.py 12 partial-runs --solver "$solver" --unchecked single \
    --sole-or 3 5 6 --only-count "$count" --seconds 28 || exit
done
python3 crown_partial_sat.py 20 5 partial-runs --solver "$solver" --expose-pairs \
  --shape 3 2 1 --seconds 135
```

## Exact minimum for two crowns

With single-use original ports everywhere, the remaining case of a pure gate read twice is excluded by the first attachment to the mixed part of the circuit. An exceptional AND with one vanishing argument forces three direct pairs, all in one orientation. The three choices for the two block types in that case are excluded by `crown_exceptions_sat.py`. Thus any 20-gate circuit would have a repeated original port. [Case analysis](crown-blocks.md#исключение-однократных-исходных-чтений-при-бюджете-20)

Setting a repeated port to zero saves two gates and leaves a disjoint (4\times4) crown and a (3\times4) crown. Cross-block negative tests imply that both restricted blocks must reject every singleton. The rectangular crown with this condition needs ten gates. At a total budget of 18, deleting a whole block is tight for either choice. The proof forces one to three direct pairs, all in one orientation, with the full column of the rectangular block among them. `crown_asymmetric_sat.py` excludes the three reduced instances. [Proof for the rectangular block and the distinct-sized pair](crown-blocks.md#полная-корона-и-прямоугольный-блок) · [Ten-gate rectangle witness in Lean](CrownBlocks.lean#L257)

```sh
python3 crown_exceptions_sat.py partial-runs --solver "$solver" --seconds 90
python3 crown_rectangular_sat.py partial-runs --solver "$solver" --size 8 --seconds 30
python3 crown_rectangular_sat.py partial-runs --solver "$solver" --size 9 --seconds 85
python3 crown_asymmetric_sat.py partial-runs --solver "$solver" --seconds 115
```

These checks return `UNSAT`. The size-nine rectangle and all three asymmetric instances also passed with CaDiCaL's internal DRAT and LRAT checking enabled.
