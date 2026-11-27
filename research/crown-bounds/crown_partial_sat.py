"""Search two crowns after three to five cross-block ORs in the eight-deletion case."""

from __future__ import annotations

import argparse
from collections.abc import Sequence
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


def unequal(cnf: Cnf, old: list[int], new: list[int], tests: list[int], one: int) -> list[int]:
    differences = []
    for i in tests:
        a, b = old[i], new[i]
        if abs(a) == one:
            differences.append(-b if a == one else b)
            continue
        d = cnf.fresh()
        cnf.clause(-d, a, b)
        cnf.clause(-d, -a, -b)
        cnf.clause(d, -a, b)
        cnf.clause(d, a, -b)
        differences.append(d)
    return differences


def retained_after_pruning(cnf: Cnf, num_vars: int, reads: list[list[int]],
                           signal_present: list[int], operand_present: Sequence[tuple[int, ...]]) -> list[int]:
    root = len(signal_present) - 1
    needed = {root: signal_present[root]}
    for i in reversed(range(root)):
        routes = [cnf.conjunction(g[i], needed[num_vars + j])
                  for j, g in enumerate(reads) if i < len(g)]
        needed[i] = cnf.conjunction(signal_present[i], cnf.disjunction(*routes))
    return [cnf.conjunction(needed[num_vars + j], *ops) for j, ops in enumerate(operand_present)]


def encode(
    size: int, shape: tuple[int, int, int], *, expose_pairs: bool = False,
) -> tuple[Cnf, Topology, list[tuple[int, ...]]]:
    groups = grouped_inputs(shape)
    num_seeds = shape[0] + shape[1]
    num_vars = len(groups)
    singles = {i: group[0] for i, group in enumerate(groups) if len(group) == 1}
    num_gates = size - num_seeds
    cells, target, points = samples(groups)
    point_index = {p: i for i, p in enumerate(points)}
    negative = [i for i, value in enumerate(target) if not value]
    within = [sorted({p for cell, p in cells.items() if block(cell[0]) == block(cell[1]) == b})
              for b in range(2)]
    positive = [[p for cell, p in cells.items() if block(cell[0]) == b and edge(cell)]
                for b in range(2)]
    rich_projection = size == 20 and expose_pairs
    projection_floor = 12 if rich_projection else 11
    if rich_projection:
        kept_inputs = [{i for i, group in enumerate(groups) if any(block(x) == b for x in group)}
                       for b in range(2)]
        if projection_floor == 12:
            within = [[t for t, point in enumerate(points[:len(target)]) if inputs.issuperset(point)]
                      for inputs in kept_inputs]
    diagonal = {
        (a, b) for a, b in combinations(singles, 2)
        if not rich_projection and singles[b] == singles[a] + ROWS
    }
    forbidden = {}
    neighbor_tests = {}
    orientation_bound = expose_pairs and (num_seeds == 4 or size == 20)
    for i, originals in enumerate(groups):
        if i not in singles and not orientation_bound:
            continue
        forbidden[i] = set()
        neighbors = set()
        for x in originals:
            side = x // ROWS
            adjacent = {p[1 - side] for p in CELLS if p[side] == x and edge(p)}
            neighbors.update(adjacent)
            comparisons = (cells[p] for p in CELLS if p[1 - side] in adjacent and not edge(p))
            singletons = (point_index[(j,)] for j, group in enumerate(groups)
                          if any(y != x and y // ROWS == side for y in group))
            if orientation_bound:
                forbidden[i].update(comparisons)
                forbidden[i].update(singletons)
            else:
                forbidden[i] = set(comparisons) | set(singletons)
        if rich_projection and i in singles:
            forbidden[i].update(point_index[(j,)] for j in kept_inputs[block(singles[i])])
        if i not in singles:
            neighbor_tests[i] = [point_index[(j,)] for j, group in enumerate(groups) if neighbors.intersection(group)]

    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    wires = [[one if i in p else -one for p in points] for i in range(num_vars)]
    topology: Topology = []
    reads = []
    top_retained: list[list[int]] = [[], []]
    redundant: list[list[int]] = [[], []]
    operand_present: list[list[tuple[int, int]]] = [[], []]
    signal_present = [[cnf.disjunction(*(row[p] for p in positive[b])) for row in wires] for b in range(2)]
    maximal_pairing = size == 19 or expose_pairs
    if maximal_pairing:
        forked = [-one if i in singles else cnf.fresh() for i in range(num_vars + num_gates - 1)]
        exposed = [one if expose_pairs or i in singles else -one for i in range(num_vars)]
        if rich_projection and shape == (2, 2, 0):
            # Both 12-gate projections require each of the four paired ports
            # to be reused. A sole first read can fold away in at most one.
            for seed in range(num_seeds):
                cnf.clause(forked[seed])
    three_seed_bound = size == 19 and num_seeds == 3
    pure_positive = []
    if three_seed_bound or orientation_bound:
        seed_only = [one] * num_seeds + [-one] * (num_vars - num_seeds)
        first_attachment = []
        seed_singletons = [point_index[(i,)] for i in range(num_seeds)]
        pure_positive = [p for tests in positive for p in tests if min(points[p]) >= num_seeds]
        pure_wires = [cnf.disjunction(*(row[p] for p in pure_positive)) for row in wires]
        pure_operands = []
    if three_seed_bound:
        first_argument = [-one] * num_vars
        attachable = [i for i, x in singles.items() if x < 4 or x >= 12]
        ab, ac, bc = (point_index[p] for p in ((0, 1), (0, 2), (1, 2)))
    if orientation_bound:
        orient = (range(shape[0]), range(shape[0], num_seeds))
        same_orientation = [[point_index[p] for p in combinations(indices, 2)] for indices in orient]
        seed_pairs = [point_index[(i, j)] for i in orient[0] for j in orient[1]]
        seed_edges = [t for t in seed_pairs if target[t]]
        seed_diagonals = [t for t in seed_pairs if not target[t]]
        port_orientation = [[i for i, x in singles.items() if (x // ROWS != block(x)) == bool(k)]
                            for k in range(2)]
        by_orientation = [[-one] * num_vars for _ in range(2)]

    for index in range(num_gates):
        (left, right, is_or), (a, c), out = gate(cnf, wires)
        topology.append((left, right, is_or))
        reads.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        direct_diagonals = {(i, j): cnf.conjunction(left[i], right[j]) for i, j in diagonal}
        if maximal_pairing:
            carries = [cnf.disjunction(*(cnf.conjunction(chosen, carries_port, -forked[i])
                                         for i, (chosen, carries_port) in enumerate(zip(operand, exposed))))
                       for operand in (left, right)]
            direct_diagonal = cnf.disjunction(*direct_diagonals.values())
            cnf.clause(-is_or, -carries[0], -carries[1], direct_diagonal)
            carry = cnf.disjunction(*carries)
            exposed.append(cnf.conjunction(is_or, carry) if expose_pairs else
                           cnf.conjunction(is_or, -direct_diagonal, carry))
        if three_seed_bound:
            pure_arg = cnf.disjunction(*(left[i] for i in attachable))
            mixed_arg = cnf.disjunction(*(cnf.conjunction(right[i], first_argument[i])
                                          for i in range(num_vars, len(wires))))
            first_attachment.append(cnf.conjunction(pure_arg, mixed_arg))
        if orientation_bound:
            for raw_ports, possible in zip(port_orientation, by_orientation):
                pure_arg = cnf.disjunction(*(left[i] for i in raw_ports))
                mixed_arg = cnf.disjunction(*(cnf.conjunction(right[i], possible[i])
                                              for i in range(num_vars, len(wires))))
                first_attachment.append(cnf.conjunction(pure_arg, mixed_arg))
        if three_seed_bound or orientation_bound:
            seeded = [cnf.disjunction(*(cnf.conjunction(chosen, only)
                                        for chosen, only in zip(operand, seed_only)))
                      for operand in (left, right)]
            seed_only.append(cnf.conjunction(*seeded))
        if three_seed_bound:
            only_bc = cnf.conjunction(-out[ac], out[bc])
            only_ac = cnf.conjunction(out[ac], -out[bc])
            pair_support = only_bc if shape[2] else cnf.disjunction(only_ac, only_bc)
            first_argument.append(cnf.conjunction(seed_only[-1], out[ab], pair_support,
                                                  *(-out[i] for i in seed_singletons)))
        if orientation_bound:
            positive_pair = cnf.disjunction(*(out[t] for t in seed_edges))
            negative_pair = [cnf.disjunction(*(out[t] for t in tests)) for tests in same_orientation]
            base = cnf.conjunction(seed_only[-1], positive_pair, *(-out[t] for t in seed_singletons + seed_diagonals))
            for k in range(2):
                by_orientation[k].append(cnf.conjunction(base, negative_pair[k], -negative_pair[1 - k]))
        if pure_positive:
            pure_wires.append(cnf.disjunction(*(out[p] for p in pure_positive)))
            pure_operands.append(tuple(cnf.disjunction(*(v[p] for p in pure_positive)) for v in (a, c)))
        cnf.clause(*(out[t] for tests in positive for t in tests))
        unsafe = cnf.disjunction(*(out[t] for t in negative))
        for operand in (a, c):
            cnf.clause(-is_or, -unsafe, *(operand[t] for t in negative))
        for i, forbidden_tests in forbidden.items():
            for selected, other in ((left[i], c), (right[i], a)):
                if i in singles:
                    cnf.clause(-selected, is_or)
                    for t in forbidden_tests:
                        cnf.clause(-selected, -other[t])
                else:
                    for t in forbidden_tests:
                        cnf.clause(-selected, forked[i], -is_or, -other[t])
                    for t in neighbor_tests[i]:
                        cnf.clause(-selected, forked[i], is_or, other[t])
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
            allowed = [flag for (i, _), flag in direct_diagonals.items() if block(singles[i]) == b]
            cnf.clause(-out[p], out[q], *allowed)
            retained = cnf.conjunction(a_top, c_top)
            top_retained[b].append(retained)
            allow_equal = cnf.fresh() if size - 8 > projection_floor else -one
            redundant[b].append(allow_equal)
            # After basic folding, every earlier signal is still available
            # as an input, an earlier retained gate, or a folded wire.
            for previous in wires:
                cnf.clause(-retained, allow_equal, *unequal(cnf, previous, out, within[b], one))
            cnf.clause(-retained, allow_equal, *(cnf.conjunction(a[t], -c[t]) for t in within[b]))
            cnf.clause(-retained, allow_equal, *(cnf.conjunction(c[t], -a[t]) for t in within[b]))
            operand_present[b].append(tuple(cnf.disjunction(*(v[t] for t in positive[b])) for v in (a, c)))
            signal_present[b].append(cnf.disjunction(*(out[t] for t in positive[b])))
        if index:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, wires[-1][:-2], out[:-2], -one))
        wires.append(out)

    if three_seed_bound or orientation_bound:
        cnf.clause(*first_attachment)
    if pure_positive:
        pure_kept = retained_after_pruning(cnf, num_vars, reads, pure_wires, pure_operands)
        essential = {i for p in pure_positive for i in points[p]}
        has_missing_corner = num_seeds == 3 or shape == (2, 2, 1)
        pure_minimum = len(essential) - 1 + int(has_missing_corner)
        cnf.at_most([-present for present in pure_kept], num_gates - pure_minimum)
        pure_ands = [cnf.conjunction(present, -is_or) for present, (_, _, is_or) in zip(pure_kept, topology)]
        two_ands = has_missing_corner or size == 20 and shape == (2, 2, 2)
        cnf.at_most([-present for present in pure_ands], num_gates - (2 if two_ands else 1))
    for i, expected in enumerate(target):
        cnf.clause(wires[-1][i] if expected else -wires[-1][i])
    for i in range(num_vars + num_gates - 1):
        used = [g[i] for g in reads if i < len(g)]
        cnf.clause(*used)
        if i in singles:
            cnf.at_most(used, 1)
        elif maximal_pairing:
            if len(used) == 1:
                cnf.clause(-forked[i])
            else:
                cnf.at_most(used, 1, escape=forked[i])
                cnf.at_most([-use for use in used], len(used) - 2, escape=-forked[i])
    if maximal_pairing:
        cnf.at_most([forked[i] for i in range(num_vars + num_gates - 1) if i not in singles], size - 15)
    for b in range(2):
        cnf.at_most(top_retained[b], size - 8)
        cnf.at_most([-present for present in top_retained[b]], 8 - num_seeds)
        cnf.at_most(redundant[b], size - 8 - projection_floor)
        kept = retained_after_pruning(cnf, num_vars, reads, signal_present[b], operand_present[b])
        cnf.at_most([-present for present in kept], num_gates - projection_floor)
        if projection_floor == 12:
            for binary, trimmed in zip(top_retained[b], kept):
                cnf.clause(-binary, trimmed)
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
    parser.add_argument("--shape", type=int, nargs=3, action="append", metavar=("P", "Q", "OVERLAP"),
                        help="select a case of the given number of pairs; may be repeated")
    parser.add_argument("--expose-pairs", action="store_true",
                        help="apply the OR-region constraint to paired and individual ports")
    args = parser.parse_args()
    all_shapes = shapes(args.pairs)
    selected = [tuple(shape) for shape in args.shape] if args.shape else all_shapes
    if any(shape not in all_shapes for shape in selected):
        parser.error(f"the available shapes for {args.pairs} pairs are {all_shapes}")
    for shape in selected:
        cnf, topology, groups = encode(args.size, shape, expose_pairs=args.expose_pairs)
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
