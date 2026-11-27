"""The three-by-four crown with all singleton tests specified as negative."""

from __future__ import annotations

import argparse
from itertools import combinations, permutations
from pathlib import Path
import subprocess

from crown_blocks_sat import Cnf
from crown_partial_sat import gate, retained_after_pruning, unequal
from crown_quotient_sat import smaller_table


def run(directory: Path, solver: Path, seconds: int, size: int) -> None:
    points = [*((i,) for i in range(7)), *((r, c) for r in range(3) for c in range(3, 7)), tuple(range(6))]
    target = [len(p) == 2 and p[0] != p[1] - 3 for p in points[:-1]]
    positive = [i for i, good in enumerate(target) if good]
    projected = [i for i in range(len(target)) if 6 not in points[i]]
    kept_positive = [i for i in positive if 6 not in points[i]]
    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    if size == 9:
        repeat = [cnf.fresh() for _ in range(7)]
        perms = [tuple(p[i] if i < 3 else 3 + p[i - 3] if i < 6 else 6 for i in range(7))
                 for p in permutations(range(3))]
        first_pairs = {pair for pair in combinations(range(7), 2)
                       if pair == min(tuple(sorted(p[i] for i in pair)) for p in perms)}
        neighbors = [{y for t in positive if x in points[t] for y in points[t] if y != x} for x in range(7)]
        forbids = [adjacent | {t for t in range(7, len(target)) if not target[t] and
                               any(y in points[t] for y in adjacent)} for adjacent in neighbors]
    wires = [[one if i in p else -one for p in points] for i in range(7)]
    topology, reads, binary, operand_present, spare = [], [], [], [], []
    signal_present = [cnf.disjunction(*(v[t] for t in kept_positive)) for v in wires]
    for stage in range(size):
        (left, right, op), (a, b), out = gate(cnf, wires)
        topology.append((left, right, op))
        reads.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        cnf.clause(*(out[t] for t in positive))
        if size == 9:
            for i in range(7):
                for selected, other in ((left[i], b), (right[i], a)):
                    for t in forbids[i]:
                        cnf.clause(-selected, repeat[i], -op, -other[t])
                    for t in neighbors[i]:
                        cnf.clause(-selected, repeat[i], op, other[t])
            for earlier in wires:
                cnf.clause(*unequal(cnf, earlier, out, list(range(len(target))), one))
            cnf.clause(-repeat[6], -left[6], op)
            cnf.clause(-repeat[6], -right[6], op)
            if stage == 0:
                for i, j in combinations(range(7), 2):
                    if (i, j) not in first_pairs:
                        cnf.clause(-left[i], -right[j])
        if size == 8:
            cnf.clause(-left[6], op)
            cnf.clause(-right[6], op)
        if size <= 9:
            retained = cnf.conjunction(a[-1], b[-1])
            binary.append(retained)
            redundant = cnf.fresh() if size == 9 else -one
            spare.append(redundant)
            for earlier in wires:
                if size == 8:
                    cnf.clause(-retained, *unequal(cnf, earlier, out, projected, one))
                else:
                    cnf.clause(-retained, redundant, *unequal(cnf, earlier, out, projected, one))
            operand_present.append(tuple(cnf.disjunction(*(v[t] for t in kept_positive)) for v in (a, b)))
            signal_present.append(cnf.disjunction(*(out[t] for t in kept_positive)))
        if stage > (1 if size == 9 else 0):
            cnf.clause(left[-1], right[-1], smaller_table(cnf, wires[-1][:-1], out[:-1], -one))
        wires.append(out)
    for t, expected in enumerate(target):
        cnf.clause(wires[-1][t] if expected else -wires[-1][t])
    for i in range(7 + size - 1):
        uses = [g[i] for g in reads if i < len(g)]
        cnf.clause(*uses)
        if size == 8 and i == 6:
            cnf.at_most(uses, 1)
        if size == 9 and i < 7:
            cnf.at_most(uses, 2 if i == 6 else 3)
            cnf.at_most(uses, 1, escape=repeat[i])
    if size == 9:
        cnf.at_most(repeat, 3)
        cnf.at_most(spare, 1)
    if size <= 9:
        cnf.at_most(binary, size - 1)
        kept = retained_after_pruning(cnf, 7, reads, signal_present, operand_present)
        cnf.at_most([-flag for flag in kept], size - 7)
    path = directory / f"rectangle-{size}.cnf"
    cnf.write(path)
    result = subprocess.run(["/usr/bin/nice", "-n", "8", str(solver), "-q", "-t", str(seconds),
                             str(path)], text=True, capture_output=True, timeout=seconds + 15)
    if result.returncode == 20 and "s UNSATISFIABLE" in result.stdout:
        print(size, "UNSAT")
    elif result.returncode == 10 and "s SATISFIABLE" in result.stdout:
        selected = {int(i) for line in result.stdout.splitlines() if line.startswith("v ")
                    for i in line[2:].split() if int(i) > 0}
        gates = [(op in selected, next(i for i, bit in enumerate(l) if bit in selected),
                  next(i for i, bit in enumerate(r) if bit in selected)) for l, r, op in topology]
        for point, expected in zip(points, target):
            wires = [i in point for i in range(7)]
            for op, a, b in gates:
                wires.append(wires[a] or wires[b] if op else wires[a] and wires[b])
            if wires[-1] != expected:
                raise ValueError(f"invalid circuit on {point}")
        print(size, "SAT", gates)
    elif result.returncode == 0 and "UNKNOWN" in result.stdout:
        print(size, "UNKNOWN")
    else:
        raise RuntimeError(result.stderr or result.stdout)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=30)
    parser.add_argument("--size", type=int, choices=(8, 9, 10), default=8)
    args = parser.parse_args()
    run(args.directory, args.solver, args.seconds, args.size)
