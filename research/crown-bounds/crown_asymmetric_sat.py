"""Search 18 gates for a four-by-four crown disjoint from a three-by-four crown."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path
import subprocess

from crown_blocks_sat import CELLS, INPUTS, ROWS, Cnf, block, edge
from crown_partial_sat import gate, samples, unequal, witness
from crown_quotient_sat import Topology, smaller_table


DOMAIN = tuple(cell for cell in CELLS if cell[0] != 7)


def encode(pairs: int) -> tuple[Cnf, Topology, list[tuple[int, ...]]]:
    groups = [(3, 15)] + [(i, 12 + i) for i in range(pairs - 1)]
    paired = {x for group in groups for x in group}
    groups += [(x,) for x in range(INPUTS) if x not in paired and x != 7]
    raw = {i: group[0] for i, group in enumerate(groups) if len(group) == 1}
    at = {x: i for i, group in enumerate(groups) for x in group}
    diagonals = {b: [(i, j) for i, j in combinations(raw, 2) if raw[j] == raw[i] + ROWS and block(raw[i]) == b]
                 for b in range(2)}
    raw_cols = [i for i, x in raw.items() if 12 <= x < 15]
    allowed_pairs = set(diagonals[0] + diagonals[1]) | {(0, i) for i in raw_cols}
    cells, target, points = samples(groups, DOMAIN)
    index = {p: i for i, p in enumerate(points)}
    ones = [[t for (a, b), t in cells.items() if block(a) == side and edge((a, b))] for side in range(2)]
    tests = [[t for (a, b), t in cells.items() if block(a) == block(b) == side] +
             [index[(i,)] for i, group in enumerate(groups) if any(block(x) == side for x in group)]
             for side in range(2)]
    negatives = [i for i, expected in enumerate(target) if not expected]
    neighbors = {x: {cell[1 - x // ROWS] for cell in DOMAIN if cell[x // ROWS] == x and edge(cell)}
                 for x in at}
    need = [{index[(at[y],)] for x in group for y in neighbors[x]} for group in groups]
    forbid = []
    for i, group in enumerate(groups):
        comparisons = {cells[cell] for x in group for cell in DOMAIN
                       if cell[1 - x // ROWS] in neighbors[x] and not edge(cell)}
        swap = {index[(j,)] for x in group for j, other in enumerate(groups) if i != j
                for y in other if x // ROWS == y // ROWS and neighbors[x] - neighbors[y]}
        forbid.append(comparisons | swap | need[i])

    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    num_inputs = len(groups)
    num_gates = 18 - pairs
    root = num_inputs + num_gates - 1
    forks = [-one if i in raw else cnf.fresh() for i in range(root)]
    cnf.clause(forks[0])
    wires = [[one if i in p else -one for p in points] for i in range(num_inputs)]
    carries = [one] * num_inputs
    topology: Topology = []
    reads = []
    retained = [[], []]
    pure_pairs = {pair: [] for pairs_for_block in diagonals.values() for pair in pairs_for_block}
    first_attach = []

    for stage in range(num_gates):
        (left, right, op), (a, b), out = gate(cnf, wires)
        topology.append((left, right, op))
        reads.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        cnf.clause(*(out[t] for tests in ones for t in tests))
        active_neg = cnf.disjunction(*(out[t] for t in negatives))
        for operand in (a, b):
            cnf.clause(-op, -active_neg, *(operand[t] for t in negatives))
        for i, j in combinations(range(num_inputs), 2):
            if (i in raw or j in raw) and (i, j) not in allowed_pairs:
                cnf.clause(-left[i], -right[j])
        first_attach.append(cnf.conjunction(left[0], cnf.disjunction(*(right[i] for i in raw_cols))))
        for i in range(num_inputs):
            for selected, other in ((left[i], b), (right[i], a)):
                if i in raw:
                    cnf.clause(-selected, op)
                for t in forbid[i]:
                    cnf.clause(-selected, forks[i], -op, -other[t])
                for t in need[i]:
                    cnf.clause(-selected, forks[i], op, other[t])
        diagonal = {pair: cnf.conjunction(left[pair[0]], right[pair[1]]) for pair in pure_pairs}
        for pair, flag in diagonal.items():
            pure_pairs[pair].append(flag)
        carried = [cnf.disjunction(*(cnf.conjunction(selected, carries[i], -forks[i])
                                      for i, selected in enumerate(port))) for port in (left, right)]
        cnf.clause(-op, -carried[0], -carried[1], *diagonal.values())
        carries.append(cnf.conjunction(op, cnf.disjunction(*carried)))
        for side in range(2):
            own, other = len(target) + side, len(target) + 1 - side
            survive = cnf.conjunction(a[own], b[own])
            retained[side].append(survive)
            cnf.clause(-out[own], *(out[t] for t in ones[side]))
            cnf.clause(-out[own], out[other], *(diagonal[p] for p in diagonals[side]))
            cnf.clause(-a[own], a[other], -b[other], b[own])
            for earlier in wires:
                cnf.clause(-survive, *unequal(cnf, earlier, out, tests[side], one))
            if side == 0:
                for i in range(pairs):
                    cnf.clause(forks[i], -reads[-1][i], -op, -survive)
        if stage:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, wires[-1][:-2], out[:-2], -one))
        wires.append(out)

    cnf.clause(*first_attach)
    for pair in diagonals[0]:
        cnf.clause(*pure_pairs[pair])
    for t, expected in enumerate(target):
        cnf.clause(wires[-1][t] if expected else -wires[-1][t])
    for i, split in enumerate(forks):
        uses = [g[i] for g in reads if i < len(g)]
        cnf.clause(*uses)
        cnf.at_most(uses, 1, escape=split)
        if len(uses) == 1:
            cnf.clause(-split)
        else:
            cnf.at_most([-use for use in uses], len(uses) - 2, escape=-split)
        if i >= num_inputs:
            for side in range(2):
                cnf.clause(-split, -wires[i][len(target) + side], wires[i][len(target) + 1 - side])
    cnf.at_most(forks, 4)
    for side, size in enumerate((11, 10)):
        cnf.at_most(retained[side], size)
        cnf.at_most([-flag for flag in retained[side]], num_gates - size)
    return cnf, topology, groups


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--pairs", type=int, nargs="+", choices=(1, 2, 3), default=(1, 2, 3))
    parser.add_argument("--seconds", type=int, default=90)
    args = parser.parse_args()
    for count in args.pairs:
        cnf, topology, groups = encode(count)
        path = args.directory / f"asymmetric-{count}.cnf"
        cnf.write(path)
        result = subprocess.run(["/usr/bin/nice", "-n", "8", str(args.solver), "-q", "-t", str(args.seconds),
                                 str(path)], text=True, capture_output=True, timeout=args.seconds + 15)
        if result.returncode == 10 and "s SATISFIABLE" in result.stdout:
            print(count, "SAT", groups, witness(result.stdout, topology, groups, DOMAIN), flush=True)
            break
        if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
            print(count, "UNSAT", flush=True)
        elif result.returncode == 0 and "UNKNOWN" in result.stdout:
            print(count, "UNKNOWN", flush=True)
        else:
            raise RuntimeError(result.stderr or result.stdout)
