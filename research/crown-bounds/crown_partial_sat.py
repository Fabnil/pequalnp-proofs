"""Search two crowns after three to five cross-block ORs in the eight-deletion case."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path
import subprocess

from crown_blocks_sat import CELLS, INPUTS, ROWS, Cnf, block, edge
from crown_quotient_sat import Topology, smaller_table


def shapes(pairs: int) -> list[tuple[int, int, int]]:
    return [(p, pairs - p, overlap) for p in range(2, min(4, pairs - 1) + 1)
            if p >= pairs - p for overlap in range(max(0, pairs - 4), pairs - p + 1)]


def grouped_inputs(shape: tuple[int, int, int]) -> list[tuple[int, ...]]:
    p, q, overlap = shape
    plus = range(p)
    minus = (*range(overlap), *range(p, p + q - overlap))
    groups = [(i, 12 + i) for i in plus] + [(4 + j, 8 + j) for j in minus]
    used = {x for pair in groups for x in pair}
    return groups + [(x,) for x in range(INPUTS) if x not in used]


def samples(groups: list[tuple[int, ...]]) -> tuple[dict[tuple[int, int], int], list[bool], list[tuple[int, ...]]]:
    wire = {x: i for i, group in enumerate(groups) for x in group}
    cells = {cell: tuple(sorted({wire[x] for x in cell})) for cell in CELLS}
    values: dict[tuple[int, ...], bool] = {}
    for cell, sample in cells.items():
        result = edge(cell)
        if values.setdefault(sample, result) != result:
            raise ValueError("the pairing identifies a positive and a negative cell")
    for i in range(len(groups)):
        if not any(i in sample and not value for sample, value in values.items()):
            raise ValueError("a singleton needs a negative superset")
        values[(i,)] = False
    order = {sample: i for i, sample in enumerate(values)}
    tops = [tuple(i for i, group in enumerate(groups) if any(block(x) == b for x in group))
            for b in range(2)]
    return {cell: order[sample] for cell, sample in cells.items()}, list(values.values()), [*values, *tops]


def gate(cnf: Cnf, wires: list[list[int]]):
    left = [cnf.fresh() for _ in wires]
    right = [cnf.fresh() for _ in wires]
    is_or = cnf.fresh()
    for choices in (left, right):
        cnf.clause(*choices)
        cnf.at_most(choices, 1)
    for a, choose in enumerate(left):
        for b in range(a + 1):
            cnf.clause(-choose, -right[b])
    a_bits = [cnf.fresh() for _ in wires[0]]
    b_bits = [cnf.fresh() for _ in wires[0]]
    output = [cnf.fresh() for _ in wires[0]]
    for selectors, operand in ((left, a_bits), (right, b_bits)):
        for selected, source in zip(selectors, wires):
            for bit, result in zip(source, operand):
                cnf.clause(-selected, -bit, result)
                cnf.clause(-selected, bit, -result)
    for a, b, out in zip(a_bits, b_bits, output):
        cnf.clause(-is_or, -a, out)
        cnf.clause(-is_or, -b, out)
        cnf.clause(-is_or, a, b, -out)
        cnf.clause(is_or, a, -out)
        cnf.clause(is_or, b, -out)
        cnf.clause(is_or, -a, -b, out)
    return (left, right, is_or), (a_bits, b_bits), output


def encode(size: int, shape: tuple[int, int, int]) -> tuple[Cnf, Topology, list[tuple[int, ...]]]:
    groups = grouped_inputs(shape)
    num_seeds = shape[0] + shape[1]
    num_vars = len(groups)
    singles = {i: group[0] for i, group in enumerate(groups) if len(group) == 1}
    num_gates = size - num_seeds
    cells, target, points = samples(groups)
    point_index = {p: i for i, p in enumerate(points)}
    negative = [i for i, value in enumerate(target) if not value]
    positive = [[p for cell, p in cells.items() if block(cell[0]) == b and edge(cell)]
                for b in range(2)]
    diagonal = {
        (a, b) for a, b in combinations(singles, 2)
        if singles[b] == singles[a] + ROWS
    }
    forbidden = {}
    for i, x in singles.items():
        side = x // ROWS
        neighbors = {p[1 - side] for p in CELLS if p[side] == x and edge(p)}
        compare = {cells[p] for p in CELLS if p[1 - side] in neighbors and not edge(p)}
        singletons = {point_index[(j,)] for j, group in enumerate(groups)
                      if any(y != x and y // ROWS == side for y in group)}
        forbidden[i] = compare | singletons

    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    wires = [[one if i in p else -one for p in points] for i in range(num_vars)]
    topology: Topology = []
    reads = []
    top_retained: list[list[int]] = [[], []]
    operand_present: list[list[tuple[int, int]]] = [[], []]
    signal_present = [[cnf.disjunction(*(row[p] for p in positive[b])) for row in wires] for b in range(2)]

    for index in range(num_gates):
        (left, right, is_or), (a, c), out = gate(cnf, wires)
        topology.append((left, right, is_or))
        reads.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        cnf.clause(*(out[t] for tests in positive for t in tests))
        unsafe = cnf.disjunction(*(out[t] for t in negative))
        for operand in (a, c):
            cnf.clause(-is_or, -unsafe, *(operand[t] for t in negative))
        for i, forbidden_tests in forbidden.items():
            for selected, other in ((left[i], c), (right[i], a)):
                cnf.clause(-selected, is_or)
                for t in forbidden_tests:
                    cnf.clause(-selected, -other[t])
        for i, j in combinations(range(num_vars), 2):
            if (i in singles or j in singles) and (i, j) not in diagonal:
                cnf.clause(-left[i], -right[j])
        for b in range(2):
            p = len(target) + b
            q = len(target) + 1 - b
            a_top, c_top = a[p], c[p]
            cnf.clause(is_or, a_top)
            cnf.clause(is_or, c_top)
            cnf.clause(-a_top, a[q], -c[q], c_top)
            allowed = [cnf.conjunction(left[i], right[j]) for i, j in diagonal if block(singles[i]) == b]
            cnf.clause(-out[p], out[q], *allowed)
            top_retained[b].append(cnf.conjunction(a_top, c_top))
            operand_present[b].append(tuple(cnf.disjunction(*(v[t] for t in positive[b])) for v in (a, c)))
            signal_present[b].append(cnf.disjunction(*(out[t] for t in positive[b])))
        if index:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, wires[-1][:-2], out[:-2], -one))
        wires.append(out)

    for i, expected in enumerate(target):
        cnf.clause(wires[-1][i] if expected else -wires[-1][i])
    for i in range(num_vars + num_gates - 1):
        used = [g[i] for g in reads if i < len(g)]
        cnf.clause(*used)
        if i in singles:
            cnf.at_most(used, 1)
    for b in range(2):
        cnf.at_most(top_retained[b], size - 8)
        cnf.at_most([-present for present in top_retained[b]], 8 - num_seeds)
        root = num_vars + num_gates - 1
        needed = {root: signal_present[b][root]}
        for i in reversed(range(root)):
            routes = [cnf.conjunction(g[i], needed[num_vars + j])
                      for j, g in enumerate(reads) if i < len(g)]
            needed[i] = cnf.conjunction(signal_present[b][i], cnf.disjunction(*routes))
        kept = [cnf.conjunction(needed[num_vars + j], *ops) for j, ops in enumerate(operand_present[b])]
        cnf.at_most([-present for present in kept], num_gates - 11)
    return cnf, topology, groups


def witness(output: str, topology: Topology, groups: list[tuple[int, ...]]):
    true = {int(x) for line in output.splitlines() if line.startswith("v ")
            for x in line[2:].split() if int(x) > 0}
    result = []
    for left, right, op in topology:
        a, = (i for i, flag in enumerate(left) if flag in true)
        b, = (i for i, flag in enumerate(right) if flag in true)
        result.append((op in true, a, b))
    for cell in CELLS:
        values = [any(x in cell for x in group) for group in groups]
        for is_or, a, b in result:
            values.append((values[a] or values[b]) if is_or else (values[a] and values[b]))
        if values[-1] != edge(cell):
            raise ValueError(f"decoded circuit fails on {cell}")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("size", type=int, choices=(19, 20))
    parser.add_argument("pairs", type=int, choices=(3, 4, 5))
    parser.add_argument("directory", type=Path)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=60)
    args = parser.parse_args()
    for shape in shapes(args.pairs):
        cnf, topology, groups = encode(args.size, shape)
        key = "-".join(map(str, shape))
        path = args.directory / f"partial-{args.size}-{key}.cnf"
        cnf.write(path)
        result = subprocess.run(["/usr/bin/nice", "-n", "8", str(args.solver), "-q", "-t", str(args.seconds),
                                 str(path)], text=True, capture_output=True, timeout=args.seconds + 15)
        lines = result.stdout.splitlines()
        if result.returncode == 10 and "s SATISFIABLE" in lines:
            print(args.size, shape, "SAT", groups, witness(result.stdout, topology, groups), flush=True)
            return
        if result.returncode == 20 and "s UNSATISFIABLE" in lines:
            print(args.size, shape, "UNSAT", flush=True)
            continue
        if result.returncode == 0 and ("c UNKNOWN" in lines or "s UNKNOWN" in lines):
            print(args.size, shape, "UNKNOWN", flush=True)
            continue
        raise RuntimeError(result.stderr or result.stdout)


if __name__ == "__main__":
    main()
