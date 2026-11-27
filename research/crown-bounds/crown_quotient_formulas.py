"""Exact truth-table search for quotient formulas with specified repeated inputs."""

from __future__ import annotations

import argparse
from functools import cache
from itertools import product
from time import monotonic

from crown_quotient_sat import EXTRA_EDGE, INPUTS, TESTS, graph, repeated_sets


INPUT_TABLES = tuple(sum(1 << i for i, sample in enumerate(TESTS) if x in sample)
                     for x in range(INPUTS))
TEST_INDEX = {sample: i for i, sample in enumerate(TESTS)}


class SearchLimit(Exception):
    pass


def splits(counts: tuple[int, ...]):
    for left in product(*(range(c + 1) for c in counts)):
        if not any(left) or left == counts:
            continue
        right = tuple(c - a for c, a in zip(counts, left))
        if left <= right:
            yield left, right


def find_formula(repeated: tuple[int, ...], seconds: float, table_limit: int,
                 extra_edge: tuple[int, int] | None = None) -> tuple[object | None, int, int]:
    """Search one multiplicity profile, keeping all distinct feasible tables."""
    maximum = tuple(2 if x in repeated else 1 for x in range(INPUTS))
    unique = tuple(x for x in range(INPUTS) if x not in repeated)
    edges, target = graph(extra_edge)
    positive_table = sum(1 << i for i, value in enumerate(target) if value)
    negative_table = sum(1 << i for i, value in enumerate(target) if not value)
    neighbors = tuple({b if a == x else a for a, b in edges if x in (a, b)} for x in range(INPUTS))
    deadline = monotonic() + seconds
    stored = 0
    comparisons = 0

    @cache
    def masks(present: tuple[int, ...]) -> tuple[int, int]:
        on = 0
        off = 0
        for x in present:
            for y in neighbors[x]:
                on |= 1 << TEST_INDEX[tuple(sorted((x, y)))]
                off |= 1 << TEST_INDEX[(y,)]
            for z in present:
                if z == x:
                    continue
                for y in neighbors[x] - neighbors[z]:
                    comparator = (z,) if z == y else tuple(sorted((z, y)))
                    off |= 1 << TEST_INDEX[comparator]
        return on, off

    @cache
    def tables(counts: tuple[int, ...]) -> frozenset[int]:
        nonlocal stored, comparisons
        if monotonic() > deadline:
            raise SearchLimit
        if sum(counts) == 1:
            return frozenset((INPUT_TABLES[counts.index(1)],))
        on, off = masks(tuple(x for x in unique if counts[x]))
        root = counts == maximum
        if root:
            on, off = positive_table, negative_table
        if on & off:
            return frozenset()
        found = set()
        for left, right in splits(counts):
            left_tables, right_tables = tables(left), tables(right)
            if root:
                left_tables = tuple(x for x in left_tables if x & on == on or x & off == 0)
                right_tables = tuple(x for x in right_tables if x & on == on or x & off == 0)
            for a in left_tables:
                for b in right_tables:
                    comparisons += 1
                    if comparisons % 8192 == 0:
                        if monotonic() > deadline or stored + len(found) > table_limit:
                            raise SearchLimit
                    meet = a & b
                    if meet not in (a, b) and meet & positive_table and meet & on == on and not meet & off:
                        if root:
                            return frozenset((meet,))
                        found.add(meet)
                    if bool(a & negative_table) != bool(b & negative_table):
                        continue
                    join = a | b
                    if join not in (a, b) and join & positive_table and join & on == on and not join & off:
                        if root:
                            return frozenset((join,))
                        found.add(join)
        stored += len(found)
        return frozenset(found)

    def witness(counts: tuple[int, ...], value: int):
        if sum(counts) == 1:
            return counts.index(1)
        for left, right in splits(counts):
            for a in tables(left):
                for b in tables(right):
                    if a & b == value:
                        return ("and", witness(left, a), witness(right, b))
                    if a | b == value:
                        return ("or", witness(left, a), witness(right, b))
        raise ValueError("the formula table has no recorded decomposition")

    answer = witness(maximum, positive_table) if positive_table in tables(maximum) else None
    return answer, stored, comparisons


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--tables", type=int, default=600000)
    parser.add_argument("--extra-edge", action="store_true", help="also accept the pair (6, 7)")
    parser.add_argument("--repeats", type=int, choices=(3, 4, 5), default=5)
    args = parser.parse_args()
    extra = EXTRA_EDGE if args.extra_edge else None
    for repeated in repeated_sets(args.repeats, extra):
        key = sum(1 << x for x in repeated)
        try:
            answer, stored, attempts = find_formula(repeated, args.seconds, args.tables, extra)
        except SearchLimit:
            print(f"{key:02x} {repeated} UNKNOWN", flush=True)
            continue
        print(f"{key:02x} {repeated} {'SAT' if answer is not None else 'UNSAT'}; "
              f"{stored} cached tables, {attempts} combinations", flush=True)
        if answer is not None:
            print(answer, flush=True)
            return


if __name__ == "__main__":
    main()
