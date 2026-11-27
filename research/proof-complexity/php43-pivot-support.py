"""Compute the minimum axiom supports of the two halves of each final parity pivot."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations
import json
from pathlib import Path
import sys


ROWS, COLS = 4, 3
NUM_VARIABLES = ROWS * COLS
UNIVERSE = range(1 << NUM_VARIABLES)
ROW_MASKS = [7 << (COLS * i) for i in range(ROWS)]
COLLISIONS = [1 << (COLS * i + h) | 1 << (COLS * j + h)
              for h in range(COLS) for i, j in combinations(range(ROWS), 2)]
ASSIGNMENT_PARITY = [bin(a).count('1') % 2 for a in UNIVERSE]


def violated(a):
    absent = sum(1 << i for i, row in enumerate(ROW_MASKS) if a & row == 0)
    together = sum(1 << (ROWS + i) for i, pair in enumerate(COLLISIONS) if a & pair == pair)
    return absent | together


def orbits():
    remaining = set(UNIVERSE) - {0}
    maps = [tuple(p[i] * COLS + q[h] for i in range(ROWS) for h in range(COLS))
            for p in permutations(range(ROWS)) for q in permutations(range(COLS))]
    while remaining:
        form = min(remaining)
        wires = [i for i in range(NUM_VARIABLES) if form >> i & 1]
        group = {sum(1 << relabel[i] for i in wires) for relabel in maps}
        remaining -= group
        yield form, len(group)


def cardinality(mask):
    return bin(mask).count('1')


@lru_cache(maxsize=None)
def hitting_set(needed):
    if not needed:
        return 0
    choices = needed[0]
    best = None
    while choices:
        bit = choices & -choices
        choices ^= bit
        trial = bit | hitting_set(tuple(m for m in needed if not (m & bit)))
        if best is None or (cardinality(trial), trial) < (cardinality(best), best):
            best = trial
    return best


def minimum_side(masks):
    forced = 0
    for m in masks:
        if m & (m - 1) == 0:
            forced |= m
    minimal = []
    for m in sorted((v for v in masks if not (v & forced)), key=lambda v: (cardinality(v), v)):
        if not any(m & earlier == earlier for earlier in minimal):
            minimal.append(m)
    result = forced | hitting_set(tuple(minimal))
    assert all(m & result for m in masks)
    return result


def packing_side(assignment_for_mask):
    forced = [m for m in assignment_for_mask if m & (m - 1) == 0]
    taken = sum(forced)
    remaining = []
    for m in sorted((v for v in assignment_for_mask if not (v & taken)), key=lambda v: (cardinality(v), v)):
        if not any(m & earlier == earlier for earlier in remaining):
            remaining.append(m)

    @lru_cache(maxsize=None)
    def pack(masks):
        if not masks:
            return ()
        first, *tail = masks
        include = (first,) + pack(tuple(v for v in tail if not (v & first)))
        exclude = pack(tuple(tail))
        return max(include, exclude, key=len)

    chosen = tuple(forced) + pack(tuple(remaining))
    pack.cache_clear()
    assert all(not (a & b) for a, b in combinations(chosen, 2))
    return [assignment_for_mask[v] for v in chosen]


def main():
    violations = [violated(a) for a in UNIVERSE]
    all_critical = (1 << (ROWS + len(COLLISIONS))) - 1
    assert all(violations) and all(1 << i in violations for i in range(22))
    result = []
    for form, multiplicity in orbits():
        hits = [{}, {}]
        for a, bad in enumerate(violations):
            hits[ASSIGNMENT_PARITY[form & a]].setdefault(bad, a)
        a, b = map(minimum_side, hits)
        packing = list(map(packing_side, hits))
        for side, assignments in enumerate(packing):
            assert all(ASSIGNMENT_PARITY[form & a] == side for a in assignments)
            assert all(not (violations[a] & violations[b]) for a, b in combinations(assignments, 2))
        assert a | b == all_critical
        result.append(dict(pivot=form, multiplicity=multiplicity, support=[a, b],
                           sizes=[cardinality(a), cardinality(b)], overlap=cardinality(a & b),
                           packing=packing))
    result.sort(key=lambda row: (row['overlap'], row['pivot']))
    assert sum(row['multiplicity'] for row in result) == len(UNIVERSE) - 1
    histogram = Counter()
    for row in result:
        histogram[row['overlap']] += row['multiplicity']
    print(len(result), 'orbits', sorted(histogram.items()))
    print('Minimum total disjoint packing', min(sum(map(len, r['packing'])) for r in result))
    print('Minimum nonsingleton overlap', min(r['overlap'] for r in result if cardinality(r['pivot']) > 1))
    Path(sys.argv[1]).write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
