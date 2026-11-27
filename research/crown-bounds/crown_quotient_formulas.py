"""Exact truth-table search for quotient formulas with five repeated inputs."""

from __future__ import annotations

import argparse
from functools import cache
from itertools import product
from time import monotonic

from crown_quotient_sat import EDGES, INPUTS, NEGATIVES, POSITIVES, TARGET, TESTS, repeated_sets


INPUT_TABLES = tuple(sum(1 << i for i, sample in enumerate(TESTS) if x in sample)
                     for x in range(INPUTS))
TARGET_TABLE = sum(1 << i for i, bit in enumerate(TARGET) if bit)
NEGATIVE_TABLE = sum(1 << i for i in NEGATIVES)
POSITIVE_TABLE = sum(1 << i for i in POSITIVES)
TEST_INDEX = {sample: i for i, sample in enumerate(TESTS)}
NEIGHBORS = tuple({b if a == x else a for a, b in EDGES if x in (a, b)} for x in range(INPUTS))


class SearchLimit(Exception):
    pass


def find_formula(repeated: tuple[int, ...], seconds: float, table_limit: int) -> tuple[bool, int, int]:
    """Search one multiplicity profile, keeping all distinct feasible tables."""
    maximum = tuple(2 if x in repeated else 1 for x in range(INPUTS))
    unique = tuple(x for x in range(INPUTS) if x not in repeated)
    deadline = monotonic() + seconds
    stored = 0
    comparisons = 0

    @cache
    def masks(present: tuple[int, ...]) -> tuple[int, int]:
        on = 0
        off = 0
        for x in present:
            for y in NEIGHBORS[x]:
                on |= 1 << TEST_INDEX[tuple(sorted((x, y)))]
                off |= 1 << TEST_INDEX[(y,)]
            for z in present:
                if z == x:
                    continue
                for y in NEIGHBORS[x] - NEIGHBORS[z]:
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
            on, off = TARGET_TABLE, NEGATIVE_TABLE
        if on & off:
            return frozenset()
        found = set()
        for left in product(*(range(c + 1) for c in counts)):
            if not any(left) or left == counts:
                continue
            right = tuple(c - a for c, a in zip(counts, left))
            if left > right:
                continue
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
                    if meet not in (a, b) and meet & POSITIVE_TABLE and meet & on == on and not meet & off:
                        if root:
                            return frozenset((meet,))
                        found.add(meet)
                    if bool(a & NEGATIVE_TABLE) != bool(b & NEGATIVE_TABLE):
                        continue
                    join = a | b
                    if join not in (a, b) and join & POSITIVE_TABLE and join & on == on and not join & off:
                        if root:
                            return frozenset((join,))
                        found.add(join)
        stored += len(found)
        return frozenset(found)

    answer = TARGET_TABLE in tables(maximum)
    return answer, stored, comparisons


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seconds", type=float, default=30)
    parser.add_argument("--tables", type=int, default=600000)
    args = parser.parse_args()
    for repeated in repeated_sets(5):
        key = sum(1 << x for x in repeated)
        try:
            answer, stored, attempts = find_formula(repeated, args.seconds, args.tables)
        except SearchLimit:
            print(f"{key:02x} {repeated} UNKNOWN", flush=True)
            continue
        print(f"{key:02x} {repeated} {'SAT' if answer else 'UNSAT'}; "
              f"{stored} cached tables, {attempts} combinations", flush=True)


if __name__ == "__main__":
    main()
