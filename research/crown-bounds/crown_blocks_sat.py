"""Search the two-crown instance using exact gate counts and block restrictions."""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path
import subprocess


ROWS = 8
INPUTS = 2 * ROWS
CELLS = tuple((r, ROWS + c) for r in range(ROWS) for c in range(ROWS))


def block(wire: int) -> int:
    return wire % ROWS // 4


def edge(pair: tuple[int, int]) -> bool:
    row, col = pair
    return block(row) == block(col) and row % ROWS != col % ROWS


class Cnf:
    def __init__(self) -> None:
        self.variables = 0
        self.clauses: list[tuple[int, ...]] = []

    def fresh(self) -> int:
        self.variables += 1
        return self.variables

    def clause(self, *literals: int) -> None:
        self.clauses.append(literals)

    def conjunction(self, *literals: int) -> int:
        output = self.fresh()
        for literal in literals:
            self.clause(-output, literal)
        self.clause(output, *(-lit for lit in literals))
        return output

    def disjunction(self, *literals: int) -> int:
        return -self.conjunction(*(-lit for lit in literals))

    def at_most(self, literals: list[int], limit: int, escape: int | None = None) -> None:
        """Use an auxiliary prefix count, with an optional disabling literal."""
        if len(literals) <= limit:
            return
        guard = () if escape is None else (escape,)
        if limit == 0:
            for literal in literals:
                self.clause(*guard, -literal)
            return
        previous: list[int] = []
        for i, literal in enumerate(literals):
            current = [self.fresh() for _ in range(min(i + 1, limit))]
            self.clause(-literal, current[0])
            for j, count in enumerate(previous):
                self.clause(-count, current[j])
                if j + 1 < limit:
                    self.clause(-count, -literal, current[j + 1])
                else:
                    self.clause(*guard, -count, -literal)
            previous = current

    def write(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as stream:
            stream.write(f"p cnf {self.variables} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(map(str, (*clause, 0))) + "\n")


def encode(size: int) -> tuple[Cnf, list[tuple[list[int], list[int], int]]]:
    """Necessary constraints on any minimal circuit of size 19 or 20."""
    if size not in (19, 20):
        raise ValueError("the projection bounds only apply here to sizes 19 and 20")

    cnf = Cnf()
    one = cnf.fresh()
    cnf.clause(one)
    top_cases = tuple(tuple(i for i in range(INPUTS) if block(i) == b) for b in range(2))
    cases = (*CELLS, *top_cases)
    values = [[one if i in point else -one for point in cases] for i in range(INPUTS)]
    accepted = [[i for i, point in enumerate(CELLS) if edge(point) and block(point[0]) == b]
                for b in range(2)]
    positive = accepted[0] + accepted[1]
    negative = [i for i, point in enumerate(CELLS) if not edge(point)]
    repeat = [cnf.fresh() for _ in range(INPUTS)]
    topology = []
    reads = []
    live_operands = []
    positive_inputs = [tuple(one if block(i) == b else -one for b in range(2))
                       for i in range(INPUTS)]
    positive_operands = []
    raw_picks = []
    merges = {point: cnf.fresh() for point in CELLS if not edge(point)}

    # Two sole-use raw ORs cannot identify samples with different answers.
    for ((r, c), first), ((s, d), second) in combinations(merges.items(), 2):
        if r != s and c != d and edge((r, d)) != edge((s, c)):
            cnf.clause(-first, -second)

    for _ in range(size):
        left = [cnf.fresh() for _ in values]
        right = [cnf.fresh() for _ in values]
        is_or = cnf.fresh()
        for selectors in (left, right):
            cnf.clause(*selectors)
            cnf.at_most(selectors, 1)
        for a, selected in enumerate(left):
            for b in range(a + 1):
                cnf.clause(-selected, -right[b])
        topology.append((left, right, is_or))
        reads.append([cnf.disjunction(a, b) for a, b in zip(left, right)])
        raw_picks.append((cnf.disjunction(*left[:INPUTS]), cnf.disjunction(*right[:INPUTS])))

        left_val = [cnf.fresh() for _ in cases]
        right_val = [cnf.fresh() for _ in cases]
        output = [cnf.fresh() for _ in cases]
        for selectors, operand in ((left, left_val), (right, right_val)):
            for selected, source in zip(selectors, values):
                for bit, literal in zip(operand, source):
                    cnf.clause(-selected, -literal, bit)
                    cnf.clause(-selected, literal, -bit)
        for a, b, bit in zip(left_val, right_val, output):
            cnf.clause(-is_or, -a, bit)
            cnf.clause(-is_or, -b, bit)
            cnf.clause(-is_or, a, b, -bit)
            cnf.clause(is_or, a, -bit)
            cnf.clause(is_or, b, -bit)
            cnf.clause(is_or, -a, -b, bit)
        cnf.clause(*(output[p] for p in positive))
        left_unsafe = cnf.disjunction(*(left_val[p] for p in negative))
        right_unsafe = cnf.disjunction(*(right_val[p] for p in negative))
        unsafe = cnf.disjunction(*(output[p] for p in negative))
        # In a minimum circuit we can minimize the number of gates that
        # fire on a negative sample. A safe input of an unsafe OR can
        # instead be ORed into the final output without adding gates.
        cnf.clause(-is_or, -unsafe, left_unsafe)
        cnf.clause(-is_or, -unsafe, right_unsafe)
        values.append(output)
        live_operands.append((left_val[-2:], right_val[-2:]))
        positive_inputs.append(tuple(cnf.disjunction(*(output[p] for p in block_tests))
                                     for block_tests in accepted))
        positive_operands.append(tuple(tuple(cnf.disjunction(*(v[p] for p in block_tests))
                                             for block_tests in accepted)
                                       for v in (left_val, right_val)))

        for a, b in combinations(range(INPUTS), 2):
            choice = (-left[a], -right[b])
            if a // ROWS == b // ROWS:
                cnf.clause(*choice, is_or)
                cnf.clause(*choice, repeat[a])
                cnf.clause(*choice, repeat[b])
            elif edge((a, b)):
                cnf.clause(*choice)
            else:
                cnf.clause(*choice, is_or)
                cnf.clause(*choice, repeat[a], repeat[b], merges[a, b])

        for wire in range(INPUTS):
            side = wire // ROWS
            partners = {CELLS[p][1 - side] for p in positive if CELLS[p][side] == wire}
            for selectors, other in ((left, right_val), (right, left_val)):
                guard = (-selectors[wire], repeat[wire])
                for point_index, point in enumerate(CELLS):
                    if point[1 - side] in partners:
                        # A sole-use AND needs its partner even on the partner
                        # singleton. Monotonicity gives the entire line.
                        cnf.clause(*guard, is_or, other[point_index])
                for p in negative:
                    if CELLS[p][1 - side] in partners:
                        # A sole-use OR must lose the positive value when the
                        # row or column is replaced by a non-neighbor.
                        cnf.clause(*guard, -is_or, -other[p])

    first_left, first_right, _ = topology[0]
    # Simultaneous relabeling, block exchange and global transpose preserve the
    # matrix. Its possible first gates have these three representatives.
    cnf.clause(first_left[0])
    cnf.clause(first_right[4], first_right[8], first_right[12])

    for wire in range(INPUTS + size - 1):
        uses = [gate[wire] for gate in reads if wire < len(gate)]
        cnf.clause(*uses)
        if wire < INPUTS:
            cnf.at_most(uses, 2)
            cnf.at_most(uses, 1, escape=repeat[wire])
    for b in range(2):
        cnf.at_most([repeat[w] for w in range(INPUTS) if block(w) == b], size - 19)

    for i, point in enumerate(CELLS):
        cnf.clause(values[-1][i] if edge(point) else -values[-1][i])
    two_live = [[cnf.conjunction(a[b], c[b]) for a, c in live_operands] for b in range(2)]
    surcharge = []
    for b in range(2):
        required: dict[int, int] = {INPUTS + size - 1: positive_inputs[-1][b]}
        cnf.clause(required[INPUTS + size - 1])
        for wire in reversed(range(INPUTS + size - 1)):
            routes = [cnf.conjunction(gate[wire], required[INPUTS + i])
                      for i, gate in enumerate(reads) if wire < len(gate)]
            required[wire] = cnf.conjunction(positive_inputs[wire][b], cnf.disjunction(*routes))
            if wire < INPUTS and block(wire) == b:
                cnf.clause(required[wire])
        # Wires that never fire on a positive sample of the kept block
        # may be set to zero, even when they fire on some negative sample.
        remains = [
            cnf.conjunction(required[INPUTS + i], a[b], c[b])
            for i, (a, c) in enumerate(positive_operands)
        ]
        cnf.at_most([-gate for gate in remains], size - 11)
        cnf.at_most([-both for both in two_live[b]], size - 11)
        if size == 19:
            surcharge.append(-one)
        else:
            extra = cnf.fresh()
            other = two_live[1 - b]
            cnf.at_most([-both for both in other], 8, escape=extra)
            cnf.at_most(other, size - 9, escape=-extra)
            surcharge.append(extra)

    for i, (left, right, _) in enumerate(topology):
        gate = values[INPUTS + i]
        for b in range(2):
            # If deleting this block saves exactly eight gates, its private
            # gates form trees. Every nontrivial maximal tree is one diagonal OR.
            pairs = [cnf.conjunction(left[j], right[ROWS + j])
                     for j in range(4 * b, 4 * b + 4)]
            cnf.clause(surcharge[b], -gate[-2 + b], gate[-1 - b], *pairs)
            # If both blocks have this property, a gate that joins the
            # two private trees can only join two opposite-side raw inputs.
            a, c = live_operands[i]
            separate = (*surcharge, -a[b], a[1 - b], -c[1 - b], c[b])
            cnf.clause(*separate, raw_picks[i][0])
            cnf.clause(*separate, raw_picks[i][1])

    # When both deletions save only eight, take three direct cross-block
    # ORs first. The first two activate together on an edge in each block.
    cnf.clause(*surcharge, first_right[12])
    second_left, second_right, _ = topology[1]
    cnf.clause(*surcharge, second_left[5])
    cnf.clause(*surcharge, second_right[9])
    third_left, third_right, _ = topology[2]
    third_cases = [cnf.conjunction(third_left[a], third_right[b])
                   for a, b in ((1, 13), (2, 14), (4, 8), (6, 10))]
    cnf.clause(*surcharge, *third_cases)
    return cnf, topology


def read_model(
    output: str, topology: list[tuple[list[int], list[int], int]]
) -> list[tuple[bool, int, int]]:
    truth = {int(literal) for line in output.splitlines() if line.startswith("v ")
             for literal in line[2:].split() if int(literal) > 0}
    gates = []
    for left, right, is_or in topology:
        a, = (i for i, flag in enumerate(left) if flag in truth)
        b, = (i for i, flag in enumerate(right) if flag in truth)
        gates.append((is_or in truth, a, b))
    for point in CELLS:
        values = [i in point for i in range(INPUTS)]
        for is_or, a, b in gates:
            values.append((values[a] or values[b]) if is_or else (values[a] and values[b]))
        if values[-1] != edge(point):
            raise ValueError(f"the decoded circuit fails on {point}")
    return gates


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("size", type=int, choices=(19, 20))
    parser.add_argument("output", type=Path)
    parser.add_argument("--solver", type=Path)
    parser.add_argument("--seconds", type=int, default=120)
    args = parser.parse_args()
    cnf, topology = encode(args.size)
    cnf.write(args.output)
    print(f"{cnf.variables} variables, {len(cnf.clauses)} clauses", flush=True)
    if args.solver is None:
        return
    result = subprocess.run(["/usr/bin/nice", "-n", "8", str(args.solver), "-q",
                             "-t", str(args.seconds), str(args.output)],
                            text=True, capture_output=True, timeout=args.seconds + 15)
    status = [line for line in result.stdout.splitlines() if line.startswith("s ")]
    print(*status)
    if result.returncode == 10 and status == ["s SATISFIABLE"]:
        print(read_model(result.stdout, topology))
    elif result.returncode == 0 and (
        status == ["s UNKNOWN"] or not status and "c UNKNOWN" in result.stdout.splitlines()
    ):
        print("s UNKNOWN")
    elif result.returncode != 20 or status != ["s UNSATISFIABLE"]:
        raise SystemExit(result.stderr or result.stdout)


if __name__ == "__main__":
    main()
