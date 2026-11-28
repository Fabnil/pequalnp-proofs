"""Enumerate maximal zero rectangles of the L-meta-10025 affine-plane matrix."""

from collections import Counter
from itertools import combinations, product
import sys

ORDER = 5
POINTS = tuple(product(range(ORDER), repeat=2))
LINES = tuple(product(range(ORDER + 1), range(ORDER)))
FULL = (1 << len(LINES)) - 1
DESK_ROWS = (
    34636833, 35719234, 37884036, 42213640, 50872848,
    69345793, 71581730, 76022852, 83921032, 68227344,
    138938625, 142643714, 151068708, 135413832, 136578192,
    276906113, 285345026, 269748740, 271061032, 272670800,
    553914433, 538452098, 539017476, 541132296, 545392688,
)


def incident(point, line):
    x, y = point
    slope, offset = line
    if slope == ORDER:
        return x == offset
    return (y - slope * x) % ORDER == offset


def popcount(word):
    return bin(word).count('1')


def indices(word):
    while word:
        bit = word & -word
        yield bit.bit_length() - 1
        word ^= bit


def maximal_rectangles(points):
    zeros = [DESK_ROWS[p] ^ FULL for p in points]
    intersections = {FULL}
    for z in zeros:
        intersections.update({z & old for old in intersections})
    for columns in sorted(intersections):
        if columns:
            rows = sum(1 << j for j, z in enumerate(zeros) if columns & z == columns)
            if rows:
                yield rows, columns, popcount(rows) * popcount(columns)


def action_on_lines():
    column_points = [tuple(i for i, p in enumerate(POINTS) if incident(p, l)) for l in LINES]
    pair_to_line = {pair: j for j, col in enumerate(column_points) for pair in combinations(col, 2)}
    assert len(pair_to_line) == 300
    for a, b, c, d in product(range(ORDER), repeat=4):
        if (a*d - b*c) % ORDER != 0:
            for u, v in product(range(ORDER), repeat=2):
                image = [ORDER*((a*x+b*y+u) % ORDER) + (c*x+d*y+v) % ORDER for x, y in POINTS]
                yield tuple(1 << pair_to_line[tuple(sorted((image[col[0]], image[col[1]])))]
                            for col in column_points)


def count_large_orbits(large):
    remaining = set(large)
    actions = tuple(action_on_lines())
    assert len(actions) == 12000
    result = Counter()
    while remaining:
        rep = min(remaining)
        bits = tuple(indices(rep))
        orbit = {sum(action[j] for j in bits) for action in actions}
        assert orbit <= remaining and all(large[img] == large[rep] for img in orbit)
        result[large[rep]] += 1
        remaining -= orbit
    return result


def restricted_instance():
    points = tuple(range(10, 25))
    cell_list = [(j, l) for j, p in enumerate(points) for l in indices(DESK_ROWS[p] ^ FULL)]
    assert len(cell_list) == 360
    entries = sorted(
        ((-area, rows, cols) for rows, cols, area in maximal_rectangles(points) if area >= 36)
    )
    assert entries[0][0] == -54 and all(area == -54 or area >= -50 for area, _, _ in entries)
    # Every invertible map of this form preserves the three retained parallel lines.
    actions = []
    for swap, u, v, w in product(range(2), range(1, ORDER), range(ORDER), range(ORDER)):
        image = []
        for p in points:
            x, y = POINTS[p]
            new_x = (1-x if swap else x) % ORDER
            new_y = (u*y + v*x + w) % ORDER
            image.append(points.index(ORDER*new_x + new_y))
        assert len(set(image)) == len(points)
        actions.append(image)
    remaining = {rows for area, rows, _ in entries if area == -54}
    reps = set()
    while remaining:
        rep = min(remaining)
        orbit = {sum(1 << action[j] for j in indices(rep)) for action in actions}
        assert orbit <= remaining
        remaining -= orbit
        reps.add(rep)
    anchors = [i for i, (area, rows, _) in enumerate(entries) if area == -54 and rows in reps]
    print(f'{len(entries)} restricted candidates; {len(anchors)} anchor orbit(s)', file=sys.stderr)
    print(len(entries), len(anchors), *anchors)
    for area, rows, cols in entries:
        footprint = sum(1 << i for i, (j, l) in enumerate(cell_list) if rows >> j & 1 and cols >> l & 1)
        assert popcount(footprint) == -area
        print(-area, *(footprint >> (64*j) & ((1 << 64) - 1) for j in range(6)))


def main():
    rows = tuple(sum(1 << j for j, line in enumerate(LINES) if incident(p, line)) for p in POINTS)
    assert rows == DESK_ROWS
    areas = Counter()
    large = {}
    for _, cols, area in maximal_rectangles(range(len(POINTS))):
        areas[area] += 1
        if area >= 40:
            large[cols] = area
    print(f'{sum(areas.values())} maximal rectangles; maximum area {max(areas)}', file=sys.stderr)
    print('Large rectangle counts:', sorted((a, n) for a, n in areas.items() if a >= 40), file=sys.stderr)
    orbits = count_large_orbits(large)
    print(f'{sum(orbits.values())} large rectangle orbits:', sorted(orbits.items()), file=sys.stderr)
    restricted_instance()


if __name__ == '__main__':
    main()
