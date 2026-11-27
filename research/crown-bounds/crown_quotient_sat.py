"""Synthesize the eight-wire quotient after all cross-block ORs are fixed."""

from __future__ import annotations

import argparse
from itertools import combinations, permutations
from pathlib import Path
import subprocess

from crown_blocks_sat import Cnf


INPUTS = 8
TESTS = tuple((i,) for i in range(INPUTS)) + tuple(combinations(range(INPUTS), 2))
TARGET = tuple(len(p) == 2 and p[0] < 4 <= p[1] and p[0] != p[1] - 4 for p in TESTS)
POSITIVES = tuple(i for i, value in enumerate(TARGET) if value)
NEGATIVES = tuple(i for i, value in enumerate(TARGET) if not value)
EDGES = {TESTS[i] for i in POSITIVES}
Topology = list[tuple[list[int], list[int], int]]
EXTRA_EDGE = (6, 7)
UNCHECKED_PAIRS = {
    "overlap-0": ((0, 1), (6, 7)),
    "overlap-1": ((0, 1), (4, 6)),
    "overlap-2": ((0, 1), (4, 5)),
    "disjoint": ((4, 5), (6, 7)),
    "triangle": ((5, 6), (5, 7), (6, 7)),
    "triangle-overlap-1": ((0, 1), (5, 6), (5, 7), (6, 7)),
    "triangle-overlap-2": ((0, 1), (4, 5), (4, 6), (5, 6)),
    "triangles-overlap-2": ((0, 1), (0, 2), (1, 2), (5, 6), (5, 7), (6, 7)),
    "triangles-overlap-3": ((0, 1), (0, 2), (1, 2), (4, 5), (4, 6), (5, 6)),
    "single": ((5, 6),),
    "single-shifted": ((6, 7),),
}


def repeated_sets(count: int, extra_edge: tuple[int, int] | None = None,
                  unchecked: tuple[tuple[int, int], ...] = (), *,
                  sole_or: tuple[int, ...] = ()) -> list[tuple[int, ...]]:
    """One representative under simultaneous relabeling and side exchange."""
    representatives = []
    seen = set()
    relabelings = [
        tuple(labels[w % 4] + 4 * ((w // 4) ^ exchange) for w in range(INPUTS))
        for labels in permutations(range(4)) for exchange in (0, 1)
    ]
    if extra_edge is not None:
        relabelings = [p for p in relabelings if tuple(sorted(p[w] for w in extra_edge)) == extra_edge]
    if unchecked:
        unchecked_set = set(unchecked)
        relabelings = [p for p in relabelings if {tuple(sorted(p[w] for w in pair))
                                                 for pair in unchecked} == unchecked_set]
    if sole_or:
        or_ports = set(sole_or)
        relabelings = [p for p in relabelings if {p[i] for i in sole_or} == or_ports]
    candidates = [i for i in range(INPUTS) if i not in sole_or]
    for repeated in combinations(candidates, count):
        if repeated in seen:
            continue
        representatives.append(repeated)
        seen.update(tuple(sorted(p[w] for w in repeated)) for p in relabelings)
    return representatives


def graph(extra_edge: tuple[int, int] | None, unchecked: tuple[tuple[int, int], ...] = ()
          ) -> tuple[set[tuple[int, int]], tuple[bool | None, ...]]:
    edges = EDGES if extra_edge is None else EDGES | {extra_edge}
    return edges, tuple(None if sample in unchecked else sample in edges for sample in TESTS)


def smaller_table(cnf: Cnf, before: list[int], after: list[int], false: int) -> int:
    """Compare two bit tables, scanning from their least significant entries."""
    less = false
    for a, b in zip(before, after):
        equal = cnf.disjunction(cnf.conjunction(a, b), cnf.conjunction(-a, -b))
        less = cnf.disjunction(cnf.conjunction(-a, b), cnf.conjunction(equal, less))
    return less


def encode(size: int, repeated: tuple[int, ...],
           extra_edge: tuple[int, int] | None = None,
           unchecked: tuple[tuple[int, int], ...] = (), *,
           sole_or: tuple[int, ...] = ()) -> tuple[Cnf, Topology]:
    if set(repeated).intersection(sole_or):
        raise ValueError("the OR ports must be read once")
    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    tables = [[one if wire in test else -one for test in TESTS] for wire in range(INPUTS)]
    edges, target = graph(extra_edge, unchecked)
    accepted = tuple(i for i, result in enumerate(target) if result is True)
    rejected = tuple(i for i, result in enumerate(target) if result is False)
    neighbors = [{b if a == w else a for a, b in edges if w in (a, b)} for w in range(INPUTS)]
    possible_neighbors = [{b if a == w else a for a, b in unchecked if w in (a, b)} | n
                          for w, n in enumerate(neighbors)]
    if any(len(n) < 3 for n in neighbors) or any(
        a <= b for i, a in enumerate(neighbors) for j, b in enumerate(possible_neighbors) if i != j
    ):
        raise ValueError("each input needs at least three neighbors and a distinguishing test against every other input")
    topology: Topology = []
    reads = []

    for gate in range(size):
        left = [cnf.fresh() for _ in tables]
        right = [cnf.fresh() for _ in tables]
        is_or = cnf.fresh()
        topology.append((left, right, is_or))
        reads.append([cnf.disjunction(a, b) for a, b in zip(left, right)])
        for selectors in (left, right):
            cnf.clause(*selectors)
            cnf.at_most(selectors, 1)
        for a, selected in enumerate(left):
            for b in range(a + 1):
                cnf.clause(-selected, -right[b])

        a_bits = [cnf.fresh() for _ in TESTS]
        b_bits = [cnf.fresh() for _ in TESTS]
        output = [cnf.fresh() for _ in TESTS]
        for selectors, operand in ((left, a_bits), (right, b_bits)):
            for sel, wire in zip(selectors, tables):
                for literal, bit in zip(wire, operand):
                    cnf.clause(-sel, -literal, bit)
                    cnf.clause(-sel, literal, -bit)
        for a, b, out in zip(a_bits, b_bits, output):
            cnf.clause(-is_or, -a, out)
            cnf.clause(-is_or, -b, out)
            cnf.clause(-is_or, a, b, -out)
            cnf.clause(is_or, a, -out)
            cnf.clause(is_or, b, -out)
            cnf.clause(is_or, -a, -b, out)

        # Retain only gates that matter on a positive test. Among minima,
        # choose a representative that moves safe OR operands to the output.
        cnf.clause(*(output[p] for p in accepted))
        if not sole_or:
            unsafe = cnf.disjunction(*(output[p] for p in rejected))
            for operand in (a_bits, b_bits):
                cnf.clause(-is_or, -unsafe, *(operand[p] for p in rejected))

        for a, b in combinations(range(INPUTS), 2):
            if a not in repeated or b not in repeated:
                cnf.clause(-left[a], -right[b])
            elif (a, b) not in edges:
                cnf.clause(-left[a], -right[b], is_or)
        for wire in range(INPUTS):
            if wire in repeated:
                continue
            for selectors, other in ((left, b_bits), (right, a_bits)):
                if wire in sole_or:
                    cnf.clause(-selectors[wire], is_or)
                if gate < 2 and not sole_or:
                    cnf.clause(-selectors[wire])
                for y in range(INPUTS):
                    cnf.clause(-selectors[wire], -is_or, -other[y])
                    if y in neighbors[wire]:
                        cnf.clause(-selectors[wire], is_or, other[y])
        for wire in tables[:INPUTS]:
            cnf.clause(*(b if a == -one else -b for a, b in zip(wire, output)))
        if gate:
            cnf.clause(left[-1], right[-1], smaller_table(cnf, tables[-1], output, -one))
        tables.append(output)

    extra_reads = size + 1 - INPUTS - len(repeated)
    for wire in range(INPUTS + size - 1):
        uses = [gate[wire] for gate in reads if wire < len(gate)]
        cnf.clause(*uses)
        if wire < INPUTS:
            if wire in repeated:
                cnf.at_most([-use for use in uses], len(uses) - 2)
                cnf.at_most(uses, 2 + extra_reads)
            else:
                cnf.at_most(uses, 1)
    cnf.at_most([use for gate in reads for use in gate[:INPUTS]], size + 1)
    for output, result in zip(tables[-1], target):
        if result is not None:
            cnf.clause(output if result else -output)
    return cnf, topology


def decode(output: str, topology: Topology, target: tuple[bool | None, ...]) -> list[tuple[bool, int, int]]:
    truth = {int(token) for line in output.splitlines() if line.startswith("v ")
             for token in line[2:].split() if int(token) > 0}
    gates = []
    for left, right, op in topology:
        a, = (i for i, flag in enumerate(left) if flag in truth)
        b, = (i for i, flag in enumerate(right) if flag in truth)
        gates.append((op in truth, a, b))
    for test, expected in zip(TESTS, target):
        wires = [i in test for i in range(INPUTS)]
        for is_or, a, b in gates:
            wires.append((wires[a] or wires[b]) if is_or else (wires[a] and wires[b]))
        if expected is not None and wires[-1] != expected:
            raise ValueError(f"decoded circuit fails on {test}")
    return gates


def run(solver: Path, path: Path, seconds: int, topology: Topology, target: tuple[bool | None, ...]) -> str:
    result = subprocess.run(["/usr/bin/nice", "-n", "8", str(solver), "-q", "-t", str(seconds),
                            str(path)], text=True, capture_output=True, timeout=seconds + 15)
    lines = result.stdout.splitlines()
    if result.returncode == 10 and "s SATISFIABLE" in lines:
        print(decode(result.stdout, topology, target), flush=True)
        return "SAT"
    if result.returncode == 20 and "s UNSATISFIABLE" in lines:
        return "UNSAT"
    if result.returncode == 0 and ("c UNKNOWN" in lines or "s UNKNOWN" in lines):
        return "UNKNOWN"
    raise RuntimeError(result.stderr or result.stdout)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("size", type=int, choices=(10, 11, 12))
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--seconds", type=int, default=12)
    promise = parser.add_mutually_exclusive_group()
    promise.add_argument("--extra-edge", action="store_true", help="also accept the pair (6, 7)")
    promise.add_argument("--unchecked", choices=tuple(UNCHECKED_PAIRS),
                         help="leave the indicated same-side pairs unspecified")
    parser.add_argument("--only-count", type=int, choices=(2, 3, 4, 5))
    parser.add_argument("--sole-or", type=int, nargs="+", metavar="PORT",
                        help="require these ports to be read once by an OR")
    args = parser.parse_args()
    sole_or = tuple(sorted(set(args.sole_or or [])))
    if any(i not in range(INPUTS) for i in sole_or):
        parser.error(f"port numbers must be from 0 to {INPUTS - 1}")
    extra = EXTRA_EDGE if args.extra_edge else None
    unchecked = UNCHECKED_PAIRS.get(args.unchecked, ())
    _, target = graph(extra, unchecked)
    prefix = "quotient-extra" if extra is not None else "quotient"
    if args.unchecked:
        prefix = f"quotient-{args.unchecked}"
    if sole_or:
        prefix += "-or-" + "".join(str(i) for i in sole_or)
    counts = range(2 if sole_or else 3, min(args.size - 7, INPUTS - len(sole_or)) + 1)
    if args.only_count is not None and args.only_count not in counts:
        parser.error("the repeat count is incompatible with this size")
    for count in (counts if args.only_count is None else (args.only_count,)):
        for repeated in repeated_sets(count, extra, unchecked, sole_or=sole_or):
            cnf, topology = encode(args.size, repeated, extra, unchecked, sole_or=sole_or)
            key = sum(1 << i for i in repeated)
            path = args.run_dir / f"{prefix}-{args.size}-{key:02x}.cnf"
            cnf.write(path)
            result = run(args.solver, path, args.seconds, topology, target)
            print(f"{args.size} {key:02x} {repeated} {result}", flush=True)
            if result == "SAT":
                return


if __name__ == "__main__":
    main()
