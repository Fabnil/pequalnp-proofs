"""Test whether an eleven-gate crown can omit a direct diagonal OR."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path
import subprocess

from crown_blocks_sat import Cnf
from crown_partial_sat import gate, unequal
from crown_quotient_sat import smaller_table


ROWS = 4
INPUTS = 8
SIZE = 11
CELLS = tuple((r, ROWS + c) for r in range(ROWS) for c in range(ROWS))
TESTS = tuple((x,) for x in range(INPUTS)) + CELLS
INDEX = {p: i for i, p in enumerate(TESTS)}
POSITIVES = [INDEX[(r, c)] for r, c in CELLS if r + ROWS != c]
DIAGONALS = [INDEX[(r, ROWS + r)] for r in range(ROWS)]
DELETED = [[INDEX[(r, c)] for r, c in CELLS if r + ROWS != c and r != i and c != ROWS + i]
           for i in range(ROWS)]


def encode(once: tuple[int, ...], or_region: bool = False, pair_first_or: bool = False) -> tuple[Cnf, list]:
    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    tables = [[one if u in sample else -one for sample in TESTS] for u in range(INPUTS)]
    repeats = [cnf.fresh() if i not in once else -one for i in range(INPUTS)]
    contacts = []
    input_values = []
    topology = []
    split = [cnf.fresh() for _ in range(INPUTS + SIZE - 1)] if or_region else []
    carry = [[one if i == label else -one for i in range(INPUTS)] for label in (3, 7)]

    for stage in range(SIZE):
        (left, right, op), (a, b), out = gate(cnf, tables)
        topology.append((left, right, op))
        contacts.append([cnf.disjunction(l, r) for l, r in zip(left, right)])
        input_values.append((a, b))
        cnf.clause(*(out[p] for p in POSITIVES))
        cnf.clause(-left[3], -right[7])
        if or_region:
            for state in carry:
                routes = [cnf.conjunction(read, -split[i], state[i])
                          for i, read in enumerate(contacts[-1])]
                state.append(cnf.conjunction(op, cnf.disjunction(*routes)))
            cnf.clause(-carry[0][-1], -carry[1][-1])
        if stage == 0:
            cnf.clause(left[0])
            cnf.clause(*(right[i] for i in (1, 3, 4, 5, 7)))
        elif stage >= 2:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, tables[-1], out, -one))
        for old in tables:
            cnf.clause(*unequal(cnf, old, out, list(range(INPUTS, len(TESTS))), one))
        for x, y in combinations(range(INPUTS), 2):
            choice = (-left[x], -right[y])
            if x // ROWS == y // ROWS:
                cnf.clause(*choice, op)
                cnf.clause(*choice, repeats[x])
                cnf.clause(*choice, repeats[y])
            elif y != x + ROWS:
                cnf.clause(*choice, repeats[x])
                cnf.clause(*choice, repeats[y])
            else:
                cnf.clause(*choice, op)
        for x in range(INPUTS):
            for chosen, other in ((left[x], b), (right[x], a)):
                if pair_first_or and x in (3, 7):
                    cnf.clause(-chosen, op)
                for j in range(ROWS):
                    if j == x % ROWS:
                        continue
                    neighbor = j + ROWS if x < ROWS else j
                    cnf.clause(-chosen, repeats[x], op, other[neighbor])
                    for p in (DIAGONALS[j], j, ROWS + j):
                        cnf.clause(-chosen, repeats[x], -op, -other[p])
        tables.append(out)

    final = INPUTS + SIZE - 1
    for i in range(final):
        uses = [c[i] for c in contacts if i < len(c)]
        cnf.clause(*uses)
        if i < INPUTS:
            cnf.at_most(uses, 1, escape=repeats[i])
            cnf.at_most(uses, 3)
        if or_region:
            if len(uses) == 1:
                cnf.clause(-split[i])
            else:
                cnf.at_most(uses, 1, escape=split[i])
                cnf.at_most([-use for use in uses], len(uses) - 2, escape=-split[i])
    for p in (*range(INPUTS), *DIAGONALS):
        cnf.clause(-tables[-1][p])
    for p in POSITIVES:
        cnf.clause(tables[-1][p])

    for positive in DELETED:
        active = [cnf.disjunction(*(v[p] for p in positive)) for v in tables]
        needed = {final: active[final]}
        for i in reversed(range(final)):
            routes = [cnf.conjunction(c[i], needed[INPUTS + j])
                      for j, c in enumerate(contacts) if i < len(c)]
            needed[i] = cnf.conjunction(active[i], cnf.disjunction(*routes))
        present = [cnf.conjunction(needed[INPUTS + j], cnf.disjunction(*(a[p] for p in positive)),
                                   cnf.disjunction(*(b[p] for p in positive)))
                   for j, (a, b) in enumerate(input_values)]
        cnf.at_most([-x for x in present], SIZE - 7)
    return cnf, topology


def witness(model: str, topology: list) -> list[tuple[bool, int, int]]:
    selected = {int(x) for line in model.splitlines() if line.startswith("v ")
                for x in line[2:].split() if int(x) > 0}
    gates = []
    for a, b, op in topology:
        i, = (i for i, name in enumerate(a) if name in selected)
        j, = (i for i, name in enumerate(b) if name in selected)
        gates.append((op in selected, i, j))
    for i, point in enumerate(TESTS):
        wires = [u in point for u in range(INPUTS)]
        for is_or, a, b in gates:
            wires.append(wires[a] or wires[b] if is_or else wires[a] and wires[b])
        if wires[-1] != (i in POSITIVES):
            raise ValueError(f"decoded circuit failed on {point}")
    return gates


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--ports", choices=("all-once", "pair-once", "any"), default="all-once")
    parser.add_argument("--or-region", action="store_true",
                        help="also forbid the two ports meeting along unshared OR paths")
    parser.add_argument("--pair-first-or", action="store_true",
                        help="require both ports of the examined pair to enter OR gates")
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=45)
    args = parser.parse_args()
    ports = {"all-once": tuple(range(INPUTS)), "pair-once": (3, 7), "any": ()}
    cnf, topology = encode(ports[args.ports], args.or_region, args.pair_first_or)
    cnf.write(args.output)
    result = subprocess.run(["/usr/bin/nice", "-n", "8", str(args.solver), "-q", "-t", str(args.seconds),
                             str(args.output)], capture_output=True, text=True, timeout=args.seconds + 15)
    lines = result.stdout.splitlines()
    if result.returncode == 10 and "s SATISFIABLE" in lines:
        print(args.ports, "SAT", witness(result.stdout, topology))
    elif result.returncode == 20 and "s UNSATISFIABLE" in lines:
        print(args.ports, "UNSAT")
    elif result.returncode == 0 and ("c UNKNOWN" in lines or "s UNKNOWN" in lines):
        print(args.ports, "UNKNOWN")
    else:
        raise RuntimeError(result.stderr or result.stdout)


if __name__ == "__main__":
    main()
