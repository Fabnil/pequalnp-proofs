"""Exclude the size-20 cases with an exceptional AND and no repeated raw port."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path
import subprocess

from crown_blocks_sat import CELLS, ROWS, Cnf, block, edge
from crown_partial_sat import gate, grouped_inputs, retained_after_pruning, samples, unequal, witness
from crown_quotient_sat import Topology, smaller_table


TYPES = ("clean", "fork", "and")


def encode(pairs: int, types: tuple[str, str]) -> tuple[Cnf, Topology, list[tuple[int, ...]]]:
    groups = grouped_inputs((pairs, 0, 0))
    raw = {i: group[0] for i, group in enumerate(groups) if len(group) == 1}
    raw_by_block = [[i for i, x in raw.items() if block(x) == b] for b in range(2)]
    diagonal = [[(i, j) for i, j in combinations(indices, 2) if raw[j] == raw[i] + ROWS]
                for indices in raw_by_block]
    num_vars = len(groups)
    num_gates = 20 - pairs
    root = num_vars + num_gates - 1
    cells, target, points = samples(groups)
    point_index = {p: i for i, p in enumerate(points)}
    within = [[t for (r, c), t in cells.items() if block(r) == block(c) == b] for b in range(2)]
    positive = [[t for (r, c), t in cells.items() if block(r) == b and edge((r, c))] for b in range(2)]
    negative = [i for i, value in enumerate(target) if not value]
    positives = positive[0] + positive[1]
    other_group = {x: i for i, group in enumerate(groups) for x in group}
    singletons = [point_index[(i,)] for i in range(num_vars)]
    neighbors = {x: {cell[1 - x // ROWS] for cell in CELLS if cell[x // ROWS] == x and edge(cell)}
                 for x in other_group}
    requires = [{singletons[other_group[y]] for x in group for y in neighbors[x]} for group in groups]
    forbids = []
    for group in groups:
        comparisons = {cells[cell] for x in group for cell in CELLS
                       if cell[1 - x // ROWS] in neighbors[x] and not edge(cell)}
        same_side = {singletons[i] for x in group for i, others in enumerate(groups)
                     if any(y != x and y // ROWS == x // ROWS for y in others)}
        forbids.append(comparisons | same_side)

    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    wires = [[one if i in p else -one for p in points] for i in range(num_vars)]
    forks = [cnf.fresh() for _ in range(root)]
    exposed = [one] * num_vars
    topology: Topology = []
    reads = []
    private = [[], []]
    private_diagonal = [[-one] * num_vars for _ in range(2)]
    and_cuts = [[], []]
    cut_of_raw = [[-one] * num_vars for _ in range(2)]
    binary = [[], []]
    redundant = [[], []]
    unfolded_or = [[[] for _ in groups] for _ in range(2)]
    signal_present = [[cnf.disjunction(*(row[p] for p in tests)) for row in wires] for tests in positive]
    operand_present = [[], []]
    needs_early_and = "and" in types
    if needs_early_and:
        if pairs < 3:
            cnf.clause(-one)
        prefix = [one if i < pairs else -one for i in range(num_vars)]
        first_cuts = []
    for b in range(2):
        cnf.at_most([forks[i] for i in raw_by_block[b]], 0)

    for stage in range(num_gates):
        (left, right, is_or), (a, c), out = gate(cnf, wires)
        topology.append((left, right, is_or))
        reads.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        cnf.clause(*(out[t] for t in positives))
        unsafe = cnf.disjunction(*(out[t] for t in negative))
        for operand in (a, c):
            cnf.clause(-is_or, -unsafe, *(operand[t] for t in negative))
        for i, j in combinations(raw, 2):
            selected = (-left[i], -right[j])
            if raw[i] // ROWS == raw[j] // ROWS:
                cnf.clause(*selected, is_or)
                cnf.clause(*selected, forks[i])
                cnf.clause(*selected, forks[j])
            elif edge((raw[i], raw[j])):
                cnf.clause(*selected)
            else:
                cnf.clause(*selected, is_or)
                if block(raw[i]) != block(raw[j]):
                    cnf.clause(*selected, forks[i], forks[j])
        for i in range(num_vars):
            for selected, other in ((left[i], c), (right[i], a)):
                for t in forbids[i]:
                    cnf.clause(-selected, forks[i], -is_or, -other[t])
                for t in requires[i]:
                    cnf.clause(-selected, forks[i], is_or, other[t])

        diags = [[cnf.conjunction(left[i], right[j], is_or) for i, j in diag] for diag in diagonal]
        carries = [cnf.disjunction(*(cnf.conjunction(selected, exposed[i], -forks[i])
                                     for i, selected in enumerate(operand))) for operand in (left, right)]
        cnf.clause(-is_or, -carries[0], -carries[1], *diags[0], *diags[1])
        exposed.append(cnf.conjunction(is_or, cnf.disjunction(*carries)))
        different_blocks = cnf.disjunction(*(cnf.conjunction(a[len(target) + b], -a[len(target) + 1 - b],
                                                             c[len(target) + 1 - b], -c[len(target) + b])
                                              for b in range(2)))
        for selected, source, other in ((left, a, c), (right, c, a)):
            reused = cnf.disjunction(*(cnf.conjunction(choice, split) for choice, split in zip(selected, forks)))
            for side in range(2):
                ports = [i for i, x in raw.items() if x // ROWS == side]
                unique_source = cnf.disjunction(*(cnf.conjunction(source[singletons[i]], -forks[i]) for i in ports))
                other_on_side = cnf.disjunction(*(other[singletons[i]] for i in ports))
                cnf.clause(-different_blocks, reused, -unique_source, -other_on_side)

        if needs_early_and:
            left_early, right_early = (
                cnf.disjunction(*(cnf.conjunction(chosen, prior) for chosen, prior in zip(operand, prefix)
                                  if prior != -one)) for operand in (left, right)
            )
            early = (left_early, right_early)
        first_fork = -one

        for b in range(2):
            own, other = len(target) + b, len(target) + 1 - b
            is_private = cnf.conjunction(out[own], -out[other])
            private[b].append(is_private)
            binary_in_block = cnf.conjunction(a[own], c[own])
            binary[b].append(binary_in_block)
            for i in (*raw_by_block[b], *range(pairs)):
                unfolded_or[b][i].append(cnf.conjunction(reads[-1][i], is_or, binary_in_block))
            if needs_early_and and types[b] == "fork" and stage < num_gates - 1:
                first_fork = cnf.conjunction(is_private, forks[num_vars + stage])

            if types[b] == "and":
                cut_cases, literal_cases, post_cases = [], [], []
                for orientation, (ps, pv, ms, mv) in enumerate(((left, a, right, c), (right, c, left, a))):
                    cut = cnf.conjunction(-is_or, pv[own], -pv[other], mv[own], mv[other])
                    pure_literal = cnf.disjunction(*(ps[i] for i in raw_by_block[b]))
                    pure_diag = cnf.disjunction(*(cnf.conjunction(selected, marked)
                                                  for selected, marked in zip(ps, private_diagonal[b])))
                    cnf.clause(-cut, pure_literal, pure_diag)
                    if needs_early_and:
                        first_cuts.append(cnf.conjunction(cut, early[1 - orientation]))
                    cut_cases.append(cut)
                    literal_cases.append(cnf.conjunction(cut, pure_literal))
                    post_cases.append(cnf.conjunction(is_or, pure_literal,
                        cnf.disjunction(*(cnf.conjunction(selected, marked)
                                          for selected, marked in zip(ms, cut_of_raw[b])))))
                    for i in raw_by_block[b]:
                        for t in requires[i]:
                            cnf.clause(-cut, -pv[singletons[i]], mv[t])
                cnf.clause(-is_private, *diags[b], *cut_cases, *post_cases)
                and_cuts[b].append(cnf.disjunction(*cut_cases))
                cut_of_raw[b].append(cnf.disjunction(*literal_cases))
            else:
                cnf.clause(-is_private, *diags[b])
            private_diagonal[b].append(cnf.disjunction(*diags[b]))

            spare = cnf.fresh() if types[1 - b] == "clean" else -one
            redundant[b].append(spare)
            for previous in wires:
                cnf.clause(-binary_in_block, spare, *unequal(cnf, previous, out, within[b], one))
            operand_present[b].append(tuple(cnf.disjunction(*(v[p] for p in positive[b])) for v in (a, c)))
            fires = cnf.disjunction(*(out[p] for p in positive[b]))
            signal_present[b].append(fires)
            if types[1 - b] != "clean":
                cnf.clause(-out[own], fires)
        if needs_early_and:
            prefix.append(cnf.disjunction(first_fork, cnf.conjunction(*early)))
        if stage:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, wires[-1][:-2], out[:-2], -one))
        wires.append(out)

    for i, expected in enumerate(target):
        cnf.clause(wires[-1][i] if expected else -wires[-1][i])
    if needs_early_and:
        cnf.clause(*first_cuts)
    tracked_private = [[], []]
    for i, split in enumerate(forks):
        uses = [g[i] for g in reads if i < len(g)]
        cnf.clause(*uses)
        cnf.at_most(uses, 1, escape=split)
        if len(uses) == 1:
            cnf.clause(-split)
        else:
            cnf.at_most([-use for use in uses], len(uses) - 2, escape=-split)
        if i in raw:
            cnf.at_most(uses, 2)
        elif i >= num_vars:
            for b in range(2):
                flag = private[b][i - num_vars]
                tracked_private[b].append(cnf.conjunction(flag, split))
                cnf.at_most(uses, 2, escape=-flag)
    cnf.at_most(forks, 5)

    for b in range(2):
        allowance = int(types[b] == "fork")
        cnf.at_most(tracked_private[b], allowance)
        if allowance:
            cnf.clause(*tracked_private[b])
        if types[b] == "and":
            cnf.clause(*and_cuts[b])
            cnf.at_most(and_cuts[b], 1)
        remaining = 12 if types[1 - b] == "clean" else 11
        cnf.at_most(binary[b], remaining)
        cnf.at_most([-live for live in binary[b]], num_gates - remaining)
        cnf.at_most(redundant[b], remaining - 11)
        kept = retained_after_pruning(cnf, num_vars, reads, signal_present[b], operand_present[b])
        cnf.at_most([-live for live in kept], num_gates - 11)
        if remaining == 11:
            violations = []
            for r, c in diagonal[b]:
                rr, cc = (cnf.disjunction(*unfolded_or[b][i]) for i in (r, c))
                direct = cnf.disjunction(*(cnf.conjunction(l[r], h[c], op)
                                           for l, h, op in topology))
                violations.append(cnf.conjunction(-forks[r], -forks[c], rr, cc, -direct))
            for paired in range(pairs):
                original = next(x for x in groups[paired] if block(x) == b)
                mate = other_group[(original + ROWS) % (2 * ROWS)]
                rr, cc = (cnf.disjunction(*unfolded_or[b][i]) for i in (paired, mate))
                violations.append(cnf.conjunction(-forks[paired], -forks[mate], rr, cc))
            cnf.at_most(violations, int(types[1 - b] == "and"))
    return cnf, topology, groups


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=45)
    parser.add_argument("--types", nargs=2, choices=TYPES, action="append", metavar=("FIRST", "SECOND"))
    parser.add_argument("--pairs", type=int, nargs="+", choices=range(4), default=(3,))
    args = parser.parse_args()
    types = args.types or [(a, "and") for a in TYPES]
    for kinds in types:
        if "and" not in kinds:
            parser.error("at least one block needs an exceptional AND")
        for count in args.pairs:
            cnf, topology, groups = encode(count, tuple(kinds))
            path = args.directory / f"{'-'.join(kinds)}-{count}.cnf"
            cnf.write(path)
            result = subprocess.run(["/usr/bin/nice", "-n", "8", str(args.solver), "-q", "-t", str(args.seconds),
                                     str(path)], text=True, capture_output=True, timeout=args.seconds + 15)
            lines = result.stdout.splitlines()
            if result.returncode == 10 and "s SATISFIABLE" in lines:
                print(*kinds, count, "SAT", groups, witness(result.stdout, topology, groups), flush=True)
                return
            if result.returncode == 20 and "s UNSATISFIABLE" in lines:
                print(*kinds, count, "UNSAT", flush=True)
            elif result.returncode == 0 and ("c UNKNOWN" in lines or "s UNKNOWN" in lines):
                print(*kinds, count, "UNKNOWN", flush=True)
            else:
                raise RuntimeError(result.stderr or result.stdout)


if __name__ == "__main__":
    main()
