"""Enumerate necessary singleton profiles for seven four-by-four crowns."""

from itertools import combinations_with_replacement


PROFILES = sorted(
    {(i, 0) for i in range(5)} | {(0, i) for i in range(5)} | {(1, 1)}
)
SUPPORT_COST = (0, 2, 2, 3, 3)


def orientation_possible(full: int, threes: int, free: int, common_free: int) -> bool:
    """Count the large shared profiles that the common helpers could supply."""
    if free == 3 and full >= 2:
        return False
    for counts in combinations_with_replacement(range(5), full):
        for shared_threes in range(threes + 1):
            shared = sum(counts) + shared_threes
            exclusive = 4 * full + threes - shared
            intersection = sum(SUPPORT_COST[q] for q in counts) + 2 * shared_threes
            if exclusive > free - common_free or intersection > 2 * common_free:
                continue

            used_full = sum(q > 0 for q in counts)
            completed_full = counts.count(4)
            mostly_shared = sum(q >= 3 for q in counts)
            if common_free <= 3 and completed_full and mostly_shared >= 2:
                continue
            if common_free <= 4 and completed_full >= 2 and (used_full > 2 or shared_threes):
                continue
            if common_free <= 5 and completed_full >= 3:
                continue
            return True
    return False


def remaining(budget: int, min_free: int) -> list[tuple[tuple, tuple]]:
    cases = []
    for profile in combinations_with_replacement(PROFILES, 7):
        if tuple(sorted((c, r) for r, c in profile)) < profile:
            continue
        singletons = tuple(sum(p[i] for p in profile) for i in range(2))
        free = tuple(budget - 28 + count for count in singletons)
        if min(free) < min_free:
            continue
        full = tuple(sum(p[i] == 4 for p in profile) for i in range(2))
        threes = tuple(sum(p[i] == 3 for p in profile) for i in range(2))
        allowed = tuple(
            m
            for m in range(min(free) + 1)
            if all(orientation_possible(full[i], threes[i], free[i], m) for i in range(2))
        )
        if allowed:
            cases.append(((free, full, threes, allowed), profile))
    return cases


def main() -> None:
    for budget, min_free in ((20, 1), (21, 3)):
        cases = remaining(budget, min_free)
        print(f"h={budget}: {len(cases)} profiles")
        for summary in sorted({key for key, _ in cases}):
            print(summary)


if __name__ == "__main__":
    main()
