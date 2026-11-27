"""Check the final formula for the six independent OR signals."""

from functools import lru_cache
from itertools import combinations


FLAGS = 6
FULL = (1 << (1 << FLAGS)) - 1
VARIABLE = tuple(sum(1 << x for x in range(1 << FLAGS) if x >> v & 1) for v in range(FLAGS))
BLOCKS = tuple((op, a, a + 1) for a in (0, 2, 4) for op in ("and", "or"))
BLOCK_VALUES = tuple(VARIABLE[a] & VARIABLE[b] if op == "and" else VARIABLE[a] | VARIABLE[b]
                     for op, a, b in BLOCKS)
NEGATIVE = sum(1 << ((1 << a) | (1 << b))
               for a, b in combinations(range(FLAGS), 2) if a // 2 != b // 2)
POSITIVE = sum(1 << sum(1 << v for v in triple) for triple in combinations(range(FLAGS), 3))


@lru_cache(None)
def block_formulas(mask):
    if mask & (mask - 1) == 0:
        i = mask.bit_length() - 1
        return ((BLOCK_VALUES[i], BLOCKS[i]),)
    results = []
    first = mask & -mask
    left = (mask - 1) & mask
    while left:
        if left & first:
            right = mask ^ left
            for w, p in block_formulas(left):
                for z, q in block_formulas(right):
                    results.extend(((w & z, ("and", p, q)), (w | z, ("or", p, q))))
        left = (left - 1) & mask
    return tuple(results)


@lru_cache(None)
def forced_subformulas(tree):
    """Tables after setting at most two subtrees to true, grouped by exact count."""
    if isinstance(tree, int):
        return ({VARIABLE[tree]}, {FULL}, set())
    op, left, right = tree
    left_values = forced_subformulas(left)
    right_values = forced_subformulas(right)
    result = (set(), {FULL}, set())
    for a in range(3):
        for b in range(3 - a):
            out = result[a + b]
            if op == "and":
                out.update(l & r for l in left_values[a] for r in right_values[b])
            else:
                out.update(l | r for l in left_values[a] for r in right_values[b])
    return result


def check():
    original = block_formulas((1 << len(BLOCKS)) - 1)
    candidates = [tree for table, tree in original if table & NEGATIVE == 0 and table & POSITIVE == POSITIVE]
    for tree in candidates:
        for tables in forced_subformulas(tree):
            if any(table & 1 == 0 and table & NEGATIVE == NEGATIVE for table in tables):
                raise ValueError(f"Potential output formula: {tree}")
    return len(original), len(candidates)


if __name__ == "__main__":
    tested, after_zero = check()
    print(f"Checked {tested} block formulas, {after_zero} pass when the cold input is zero.")
    print("No formula passes with the cold input also set to one.")
