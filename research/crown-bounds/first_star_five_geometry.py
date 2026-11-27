"""Enumerate necessary cover sizes for a singleton-trigger star group."""

from collections import defaultdict
from itertools import combinations
from pathlib import Path
import re


POINTS = 13
LINES = 12
LINE_SUBSETS = 1 << LINES
CARD = [bin(mask).count("1") for mask in range(1 << POINTS)]


def edges_from_lean():
    source = Path(__file__).with_name("PlaneCompletion.lean").read_text()
    edge_table = source.split("def edges", 1)[1].split("def deleted", 1)[0]
    pairs = re.findall(r"\((\d+),\s*(\d+)\)", edge_table)
    edges = [(int(point), int(line) - POINTS) for point, line in pairs]
    assert len(set(edges)) == len(edges) == 48
    assert all(0 <= point < POINTS and 0 <= line < LINES for point, line in edges)
    return edges


def neighbor_masks(edges):
    points = [0] * POINTS
    lines = [0] * LINES
    for point, line in edges:
        points[point] |= 1 << line
        lines[line] |= 1 << point
    return points, lines


def necessary_covers(edges, extra_union=False):
    graph_points, graph_lines = neighbor_masks(edges)
    modes = defaultdict(set)
    missing_noncenter_limit = 2 if extra_union else 1
    center_counts = (13,) if extra_union else (13, 14)
    largest_point_excess = max(center_counts) - LINES
    for side in ("points", "lines"):
        trigger_centers = range(LINES if side == "points" else POINTS)
        for center in trigger_centers:
            if side == "points":
                pool = [(x, l) for x, l in edges if graph_lines[center] >> x & 1 and l != center]
            else:
                pool = [(x, l) for x, l in edges if graph_points[center] >> l & 1 and x != center]

            for deleted in combinations(pool, 5):
                missed_points, missed_lines = neighbor_masks(deleted)
                if any(g == f for g, f in zip(graph_points, missed_points)):
                    continue
                if any(g == f for g, f in zip(graph_lines, missed_lines)):
                    continue

                retained_lines = [g ^ f for g, f in zip(graph_lines, missed_lines)]
                required_points = [0] * LINE_SUBSETS
                affected_points = set(point for point, _ in deleted)
                affected_lines = set(line for _, line in deleted)
                singleton_leaf_points = 0
                singleton_leaf_lines = 0
                if extra_union:
                    for point in affected_points:
                        if CARD[graph_points[point] ^ missed_points[point]] == 1:
                            singleton_leaf_points |= 1 << point
                    for line in affected_lines:
                        if CARD[retained_lines[line]] == 1:
                            singleton_leaf_lines |= 1 << line
                for omitted in range(LINE_SUBSETS):
                    if omitted:
                        bit = omitted & -omitted
                        required_points[omitted] = (
                            required_points[omitted ^ bit] | retained_lines[bit.bit_length() - 1]
                        )
                    if side == "points" and omitted >> center & 1:
                        continue
                    if side == "lines" and omitted & singleton_leaf_lines:
                        continue
                    k = CARD[omitted]
                    selected = required_points[omitted]
                    if CARD[selected] > k + largest_point_excess:
                        continue

                    if side == "points":
                        selected |= singleton_leaf_points
                        for point in affected_points:
                            if CARD[omitted & missed_points[point]] > missing_noncenter_limit:
                                selected |= 1 << point
                        minimum = CARD[selected]
                    else:
                        selected |= 1 << center
                        minimum = CARD[selected]
                        # The deleted point sets of different lines are disjoint.
                        for line in affected_lines:
                            if omitted >> line & 1:
                                missing = CARD[missed_lines[line] & ~selected]
                                minimum += max(0, missing - missing_noncenter_limit)

                    for count in center_counts:
                        point_centers = k + count - LINES
                        if minimum <= point_centers <= POINTS:
                            modes[count, side].add(k)
    return dict(modes)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extra-union", action="store_true", help="Check the one-spare 13-center case")
    args = parser.parse_args()
    actual = necessary_covers(edges_from_lean(), extra_union=args.extra_union)
    for (count, side), omitted in sorted(actual.items()):
        print(count, side, sorted(omitted))
    saturated = {
        (13, "lines"): {0, 12},
        (13, "points"): {0},
        (14, "lines"): {0, 1, 10, 11},
        (14, "points"): {0, 1, 10, 11},
    }
    one_spare = {
        (13, "lines"): {0, 1, 2, 12},
        (13, "points"): {0},
    }
    assert actual == (one_spare if args.extra_union else saturated)
