"""Exhaust the OR-only shared-stage profiles at the 26-gate margin."""

from dataclasses import dataclass
from itertools import combinations, product


INPUTS = 11


@dataclass(frozen=True)
class Group:
    profile: int
    raw_reads: int
    capacity: int


def topological_graphs(uses):
    flags = len(uses)
    choices = [
        tuple(targets for count in range(min(limit, flags - i - 1) + 1)
              for targets in combinations(range(i + 1, flags), count))
        for i, limit in enumerate(uses)
    ]
    for readers in product(*choices):
        links = tuple((i, j) for i, targets in enumerate(readers) for j in targets)
        yield links, tuple(limit - len(targets) for limit, targets in zip(uses, readers))


def supported_groups(flags, links):
    def close(mask):
        for source, target in links:
            if mask >> source & 1:
                mask |= 1 << target
        return mask

    individual = [close(1 << i) for i in range(flags)]
    yield Group(0, 2, 3)
    for mask in individual:
        yield Group(mask, 1, 2)
    for a, b in combinations(individual, 2):
        merged = a | b
        if merged != a and merged != b:
            yield Group(merged, 0, 1)


def possible_counts(groups, output_reads, inputs=INPUTS, min_support=0):
    size = 1 << len(output_reads)
    scale = 1 << (2 + sum(output_reads))

    def charges(group):
        for base in range(size):
            if base & group.profile == base:
                added = group.profile ^ base
                length = group.raw_reads + sum(
                    cap for i, cap in enumerate(output_reads) if added >> i & 1
                )
                yield base, scale >> length

    prices = [tuple(charges(group)) for group in groups]
    remaining = [0] * (len(groups) + 1)
    support = [[0] * len(output_reads) for _ in remaining]
    for i in reversed(range(len(groups))):
        remaining[i] = remaining[i + 1] + groups[i].capacity
        support[i] = [s + (groups[i].capacity if groups[i].profile >> f & 1 else 0)
                      for f, s in enumerate(support[i + 1])]

    def visit(index, needed, balances, counts, demands):
        if needed > remaining[index] or any(a > min(b, needed) for a, b in zip(demands, support[index])):
            return
        if index == len(groups):
            yield counts
            return
        price = prices[index]
        affordable = min(balances[base] // cost for base, cost in price)
        low = max(0, needed - remaining[index + 1])
        high = min(groups[index].capacity, needed, affordable)
        for count in range(low, high + 1):
            updated = balances.copy()
            for base, cost in price:
                updated[base] -= cost * count
            after = tuple(a - (count if groups[index].profile >> f & 1 else 0)
                          for f, a in enumerate(demands))
            yield from visit(index + 1, needed - count, updated, (*counts, count), after)

    yield from visit(0, inputs, [scale] * size, (), (min_support,) * len(output_reads))


def verify():
    cases = [tuple(2 + (flag == triple) for flag in range(4)) for triple in range(4)]
    cases.append((2,) * 5)
    checked = 0
    solutions = []
    for uses in cases:
        for links, output_reads in topological_graphs(uses):
            checked += 1
            groups = tuple(supported_groups(len(uses), links))
            for counts in possible_counts(groups, output_reads):
                solutions.append((uses, links, counts))
    expected = ((2,) * 5, (), (1, *(0,) * 5, *(1,) * 10))
    if solutions != [expected]:
        raise ValueError(f"Unexpected surviving layouts: {solutions}")
    return checked, expected


if __name__ == "__main__":
    count, solution = verify()
    print(f"{count} topologically labeled graphs with read counts")
    print("Only survivor:", solution)
